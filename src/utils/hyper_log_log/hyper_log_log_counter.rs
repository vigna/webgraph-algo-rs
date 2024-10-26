use super::*;
use crate::prelude::*;
use common_traits::{AsBytes, AtomicUnsignedInt, IntoAtomic, UpcastableInto};
use std::{
    hash::{BuildHasher, Hash},
    sync::atomic::Ordering,
};
use sux::{bits::BitFieldVec, traits::bit_field_slice::*};

/// Utility struct for parallel optimization.
pub struct ThreadHelper<W: Word + IntoAtomic> {
    pub(super) acc: Vec<W>,
    pub(super) mask: Vec<W>,
}

/// Concretized counter for [`HyperLogLogCounterArray`].
///
/// Each counter holds only basic information in order to reduce memory usage.
/// In particular each counter holds a shared reference to the parent [`HyperLogLogCounterArray`]
/// and the offset of the first register of the counter.
///
/// In alternative, the counter may make a local copy of the registers using the
/// [`Self::cache`] method.
pub struct HyperLogLogCounter<'a, T, W: Word + IntoAtomic, H: BuildHasher> {
    /// The reference to the parent [`HyperLogLogCounterArray`].
    pub(super) counter_array: &'a HyperLogLogCounterArray<T, W, H>,
    /// The offset of the first register of the counter.
    pub(super) offset: usize,
    /// The cached counter bits. Remeinder bits are to be considered noise and not used.
    /// The boolean value is [`true`] if the cache has been modified and needs to be
    /// committed to the backend.
    pub(super) cached_bits: Option<(BitFieldVec<W>, bool)>,
    /// Reference to an already allocated cache to help reduce allocations in parallel
    /// executions.
    pub(super) thread_helper: Option<&'a mut ThreadHelper<W>>,
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> HyperLogLogCounter<'a, T, W, H> {
    /// Returns the index of the current counter
    #[inline(always)]
    pub fn counter_index(&self) -> usize {
        // self.offset / self.counter_array.num_registers
        self.offset >> self.counter_array.log_2_num_registers
    }

    /// Returns whether the counter's cache has been modified and should be committed to the backend.
    #[inline(always)]
    pub fn is_changed(&self) -> bool {
        if let Some((_, changed)) = self.cached_bits {
            changed
        } else {
            false
        }
    }

    /// Returns whether the counter is cached or not.
    #[inline(always)]
    pub fn is_cached(&self) -> bool {
        self.cached_bits.is_some()
    }

    /// Performs a multiple precision subtraction, leaving the result in the first operand.
    /// The operands MUST have the same length.
    ///
    /// # Arguments
    /// * `x`: the first operand. This will contain the final result.
    /// * `y`: the second operand that will be subtracted from `x`.
    #[inline(always)]
    fn subtract(x: &mut [W], y: &[W]) {
        debug_assert_eq!(x.len(), y.len());
        let mut borrow = false;

        for (x_word, &y) in x.iter_mut().zip(y.iter()) {
            let mut x = *x_word;
            if !borrow {
                borrow = x < y;
            } else if x != W::ZERO {
                x = x.wrapping_sub(W::ONE);
                borrow = x < y;
            } else {
                x = x.wrapping_sub(W::ONE);
            }
            *x_word = x.wrapping_sub(y);
        }
    }

    /// Merges `other` into `self` inplace using words instead of registers and returns
    /// whether `self` was modified.
    ///
    /// `other` is not modified but `self` can be.
    ///
    /// # Arguments
    /// * `other`: the counter to merge into `self`.
    ///
    /// # Safety
    ///
    /// Calling this method while reading (ie. with [`Self::cache`] on the same counter from
    /// another instance) or writing (ie. with [`Self::commit_changes`]) from the same memory
    /// zones in the backend [`HyperLogLogCounterArray`] is [undefined behavior].
    ///
    /// Calling this method on the same counters at the same time in
    /// different directions without first calling [`Self::cache`] as
    /// is shown below is [undefined behavior]:
    /// ```no_run
    /// # use rayon::join;
    /// # use webgraph_algo::utils::HyperLogLogCounterArrayBuilder;
    /// # use webgraph_algo::prelude::*;
    /// # use anyhow::Result;
    /// # fn main() -> Result<()> {
    /// let counters = HyperLogLogCounterArrayBuilder::new()
    ///     .rsd(0.1)
    ///     .num_elements_upper_bound(10)
    ///     .build(2)?;
    /// let mut c1 = counters.get_counter(0);
    /// let mut c2 = counters.get_counter(1);
    /// let c1_shared = counters.get_counter(0);
    /// let c2_shared = counters.get_counter(1);
    /// # counters.get_counter(0).add(0);
    ///
    /// // This is undefined behavior
    /// join(|| unsafe {c1.merge_bitwise_unsafe(&c2_shared)}, || unsafe {c2.merge_bitwise_unsafe(&c1_shared)});
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// On the other hand, once the counter is cached it is fine:
    ///
    /// ```
    /// # use rayon::join;
    /// # use webgraph_algo::utils::HyperLogLogCounterArrayBuilder;
    /// # use webgraph_algo::prelude::*;
    /// # use anyhow::Result;
    /// # fn main() -> Result<()> {
    /// let counters = HyperLogLogCounterArrayBuilder::new()
    ///     .rsd(0.1)
    ///     .num_elements_upper_bound(10)
    ///     .build(2)?;
    /// let mut c1 = counters.get_counter(0);
    /// let mut c2 = counters.get_counter(1);
    /// let c1_shared = counters.get_counter(0);
    /// let c2_shared = counters.get_counter(1);
    /// # counters.get_counter(0).add(0);
    ///
    /// c1 = c1.into_owned();
    /// c2 = c2.into_owned();
    ///
    /// // This is fine
    /// join(|| unsafe {c1.merge_bitwise_unsafe(&c2_shared)}, || unsafe {c2.merge_bitwise_unsafe(&c1_shared)});
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn merge_unsafe(&mut self, other: &Self) -> bool {
        // The temporary vectors if no thread helper is used
        let mut acc_internal;
        let mut mask_internal;

        let num_words = self.counter_array.words_per_counter();
        let num_words_minus_1 = num_words - 1;
        let register_size_minus_1 = self.counter_array.register_size - 1;
        let shift_register_size_minus_1 = W::BITS - register_size_minus_1;
        let last_word_mask = self.counter_array.residual_mask;

        let msb_mask = self.counter_array.msb_mask.as_slice();
        let lsb_mask = self.counter_array.lsb_mask.as_slice();
        let (x, mut changed) = match &mut self.cached_bits {
            Some((bits, c)) => (bits.as_mut_slice(), *c),
            None => {
                let bits_offset = self.offset * self.counter_array.register_size;
                // Counters should be byte-aligned
                debug_assert!(bits_offset % 8 == 0);
                let byte_offset = bits_offset / 8;
                let num_bytes = num_words * W::BYTES;
                // We should copy whole words, not parts
                debug_assert!((num_bytes * 8) % W::BITS == 0);

                let pointer =
                    (self.counter_array.bits.as_slice().as_ptr() as *mut W).byte_add(byte_offset);
                debug_assert!(pointer.is_aligned());

                (std::slice::from_raw_parts_mut(pointer, num_words), false)
            }
        };
        let (acc, mask) = if let Some(helper) = &mut self.thread_helper {
            helper.acc.set_len(0);
            helper.mask.set_len(0);
            (&mut helper.acc, &mut helper.mask)
        } else {
            acc_internal = Vec::with_capacity(num_words);
            mask_internal = Vec::with_capacity(num_words);
            (&mut acc_internal, &mut mask_internal)
        };
        let y = match &other.cached_bits {
            Some((bits, _)) => bits.as_slice(),
            None => {
                let bits_offset = other.offset * self.counter_array.register_size;
                // Counters should be byte-aligned
                debug_assert!(bits_offset % 8 == 0);
                let byte_offset = bits_offset / 8;
                let num_bytes = num_words * W::BYTES;
                // We should copy whole words, not parts
                debug_assert!((num_bytes * 8) % W::BITS == 0);

                let pointer = (other.counter_array.bits.as_slice().as_ptr() as *const W)
                    .byte_add(byte_offset);
                debug_assert!(pointer.is_aligned());

                std::slice::from_raw_parts(pointer, num_words)
            }
        };

        // We split x, y and the masks so we treat the last word appropriately.
        let (x_last, x_slice) = x.split_last_mut().unwrap_unchecked();
        let x_last_masked = *x_last & last_word_mask;
        let (&y_last, y_slice) = y.split_last().unwrap_unchecked();
        let y_last_masked = y_last & last_word_mask;
        let (&msb_last, msb_slice) = msb_mask.split_last().unwrap_unchecked();

        /* We work in two phases. Let H_r (msb_mask) be the mask with the
         * highest bit of each register (of size r) set, and L_r (lsb_mask)
         * be the mask with the lowest bit of each register set.
         * We describe the algorithm on a single word.
         *
         * In the first phase we perform an unsigned strict register-by-register
         * comparison of x and y, using the formula
         *
         * z = ((((y | H_r) - (x & !H_r)) | (y ^ x)) ^ (y | !x)) & H_r
         *
         * Then, we generate a register-by-register mask of all ones or
         * all zeroes, depending on the result of the comparison, using the
         * formula
         *
         * (((z >> r-1 | H_r) - L_r) | H_r) ^ z
         *
         * At that point, it is trivial to select from x and y the right values.
         */

        // We load y | H_r into the accumulator.
        acc.extend(
            y_slice
                .iter()
                .zip(msb_slice)
                .map(|(&y_word, &msb_word)| y_word | msb_word),
        );
        acc.push(y_last_masked | msb_last);

        // We load x & !H_r into mask as temporary storage.
        mask.extend(
            x_slice
                .iter()
                .zip(msb_slice)
                .map(|(&x_word, &msb_word)| x_word & !msb_word),
        );
        mask.push(x_last_masked & !msb_last);

        // We subtract x & !H_r, using mask as temporary storage
        Self::subtract(acc, mask);

        // We OR with y ^ x, XOR with (y | !x), and finally AND with H_r.
        {
            let (acc_last, acc_slice) = acc.split_last_mut().unwrap_unchecked();
            acc_slice
                .iter_mut()
                .zip(x_slice.iter())
                .zip(y_slice.iter())
                .zip(msb_slice.iter())
                .for_each(|(((acc_word, &x_word), &y_word), &msb_word)| {
                    *acc_word = ((*acc_word | (y_word ^ x_word)) ^ (y_word | !x_word)) & msb_word
                });
            *acc_last = ((*acc_last | (y_last_masked ^ x_last_masked))
                ^ (y_last_masked | !x_last_masked))
                & msb_last;
        }

        // We shift by register_size - 1 places and put the result into mask.
        {
            let (mask_last, mask_slice) = mask.split_last_mut().unwrap_unchecked();
            mask_slice
                .iter_mut()
                .zip(acc[0..num_words_minus_1].iter())
                .zip(acc[1..].iter())
                .zip(msb_slice.iter())
                .rev()
                .for_each(|(((mask_word, &acc_word), &next_acc_word), &msb_word)| {
                    // W is always unsigned so the shift is always with a 0
                    *mask_word = (acc_word >> register_size_minus_1)
                        | (next_acc_word << shift_register_size_minus_1)
                        | msb_word
                });
            *mask_last = (acc[num_words_minus_1] >> register_size_minus_1) | msb_last;
        }

        // We subtract L_r from mask.
        Self::subtract(mask, lsb_mask);

        // We OR with H_r and XOR with the accumulator.
        let (mask_last, mask_slice) = mask.split_last_mut().unwrap_unchecked();
        let (&acc_last, acc_slice) = acc.split_last().unwrap_unchecked();
        mask_slice
            .iter_mut()
            .zip(msb_slice.iter())
            .zip(acc_slice.iter())
            .for_each(|((mask_word, &msb_word), &acc_word)| {
                *mask_word = (*mask_word | msb_word) ^ acc_word
            });
        *mask_last = (*mask_last | msb_last) ^ acc_last;

        // Finally, we use mask to select the right bits from x and y and store the result.
        if changed {
            x_slice
                .iter_mut()
                .zip(y_slice.iter())
                .zip(mask_slice.iter())
                .for_each(|((x_word, &y_word), &mask_word)| {
                    *x_word = *x_word ^ ((*x_word ^ y_word) & mask_word);
                });
            *x_last = (*x_last & !last_word_mask)
                | (x_last_masked ^ ((x_last_masked ^ y_last_masked) & *mask_last));
        } else {
            x_slice
                .iter_mut()
                .zip(y_slice.iter())
                .zip(mask_slice.iter())
                .for_each(|((x_word, &y_word), &mask_word)| {
                    let new_x_word = *x_word ^ ((*x_word ^ y_word) & mask_word);
                    if new_x_word != *x_word {
                        changed = true;
                        *x_word = new_x_word;
                    }
                });
            let new_x_last = (*x_last & !last_word_mask)
                | (x_last_masked ^ ((x_last_masked ^ y_last_masked) & *mask_last));
            if new_x_last != *x_last {
                changed = true;
                *x_last = new_x_last;
            }

            if changed {
                if let Some((_, cache_changed)) = self.cached_bits.as_mut() {
                    *cache_changed = changed;
                }
            }
        }

        changed
    }

    /// Cache the counter's registers.
    ///
    /// Once this method is called every change applied to this counter isn't reflected
    /// in the backend [`HyperLogLogCounterArray`] until [`Self::commit_changes`] is
    /// called.
    ///
    /// # Safety
    ///
    /// Calling this method while writing to the same memory zone in the backend
    /// [`HyperLogLogCounterArray`] (ie. with [`Self::commit_changes`] on the same counter from
    /// another instance) is [undefined behavior].
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn cache(&mut self) {
        let bits_offset = self.offset * self.counter_array.register_size;
        // Counters should be byte-aligned
        debug_assert!(bits_offset % 8 == 0);
        let byte_offset = bits_offset / 8;
        let num_words = self.counter_array.words_per_counter();
        let num_bytes = num_words * W::BYTES;
        // We should copy whole words, not parts
        debug_assert!((num_bytes * 8) % W::BITS == 0);

        let pointer =
            (self.counter_array.bits.as_slice().as_ptr() as *const u8).byte_add(byte_offset);

        let mut v = Vec::with_capacity(num_words);
        std::ptr::copy_nonoverlapping(pointer, v.as_mut_ptr() as *mut u8, num_bytes);
        v.set_len(num_words);

        self.cached_bits = Some((
            BitFieldVec::from_raw_parts(
                v,
                self.counter_array.register_size,
                self.counter_array.num_registers,
            ),
            false,
        ));
    }

    /// Sets the content of the counter to the content of the passed counter.
    ///
    /// # Arguments
    /// * `counter`: the counter from which to copy the contents.
    ///
    /// # Safety
    ///
    /// Calling this method while reading from the same memory zone in the backend
    /// [`HyperLogLogCounterArray`] (ie. with [`Self::cache`] on the same counter from
    /// another instance) is [undefined behavior].
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn set_to(&mut self, counter: &Self) {
        debug_assert_eq!(
            self.counter_array.register_size,
            counter.counter_array.register_size
        );
        debug_assert_eq!(
            self.counter_array.num_registers,
            counter.counter_array.num_registers
        );
        debug_assert_eq!(
            self.counter_array.words_per_counter(),
            counter.counter_array.words_per_counter()
        );
        debug_assert_eq!(
            self.counter_array.residual_mask,
            counter.counter_array.residual_mask
        );

        let bits_to_copy = self.counter_array.num_registers * self.counter_array.register_size;
        debug_assert!(bits_to_copy % 8 == 0);
        let bytes_to_copy = bits_to_copy / 8;

        let bits_offset = counter.offset * self.counter_array.register_size;
        // Counters should be byte-aligned
        debug_assert!(bits_offset % 8 == 0);
        let byte_offset = bits_offset / 8;

        let counter_pointer = if let Some((cached_bits, _)) = &counter.cached_bits {
            cached_bits.as_slice().as_ptr() as *const u8
        } else {
            (counter.counter_array.bits.as_slice().as_ptr() as *const u8).byte_add(byte_offset)
        };

        match &mut self.cached_bits {
            Some((bits, changed)) => {
                let cache_pointer = bits.as_mut_slice().as_mut_ptr() as *mut u8;
                std::ptr::copy_nonoverlapping(counter_pointer, cache_pointer, bytes_to_copy);

                let backend_pointer =
                    (self.counter_array.bits.as_slice().as_ptr() as *mut u8).byte_add(byte_offset);
                let backend_slice = std::slice::from_raw_parts(backend_pointer, bytes_to_copy);
                let cache_slice = std::slice::from_raw_parts(
                    bits.as_slice().as_ptr() as *const u8,
                    bytes_to_copy,
                );

                *changed = backend_slice == cache_slice;
            }
            None => {
                let bits_offset = self.offset * self.counter_array.register_size;
                // Counters should be byte-aligned
                debug_assert!(bits_offset % 8 == 0);
                let byte_offset = bits_offset / 8;

                let backend_pointer =
                    (self.counter_array.bits.as_slice().as_ptr() as *mut u8).byte_add(byte_offset);

                std::ptr::copy_nonoverlapping(counter_pointer, backend_pointer, bytes_to_copy);
            }
        }
    }

    /// Sets the couter to use the specified thread helper.
    #[inline(always)]
    pub fn use_thread_helper(&mut self, helper: &'a mut ThreadHelper<W>) {
        self.thread_helper = Some(helper);
    }

    /// Stops the counter from using the thread helper.
    #[inline(always)]
    pub fn remove_thread_helper(&mut self) {
        self.thread_helper = None;
    }
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> HyperLogLogCounter<'a, T, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    /// Sets a register of the counter to the specified new value.
    ///
    /// If the counter is cached the new value isn't propagated to the backend
    /// [`HyperLogLogCounterArray`] until [`Self::commit_changes`] is called on
    /// this counter.
    ///
    /// # Arguments
    /// * `index`: the index of the register to edit.
    /// * `new_value`: the new value to store in the register.
    #[inline(always)]
    fn set_register(&mut self, index: usize, new_value: W) {
        match &mut self.cached_bits {
            Some((bits, changed)) => {
                let old_value = bits.get(index);
                if old_value != new_value {
                    *changed = true;
                    bits.set(index, new_value)
                }
            }
            None => self.counter_array.bits.set_atomic(
                self.offset + index,
                new_value,
                Ordering::Relaxed,
            ),
        }
    }

    /// Gets the current value of the specified register.
    ///
    /// If the counter is cached and has been modified, this methods returns
    /// the value present in the local cache, not the one present in the
    /// backend.
    ///
    /// # Arguments
    /// * `index`: the index of the register to read.
    #[inline(always)]
    fn get_register(&self, index: usize) -> W {
        match &self.cached_bits {
            Some((bits, _)) => bits.get(index),
            None => self
                .counter_array
                .bits
                .get_atomic(self.offset + index, Ordering::Relaxed),
        }
    }
}

impl<
        'a,
        T: Hash,
        W: Word + TryFrom<HashResult> + UpcastableInto<HashResult> + IntoAtomic,
        H: BuildHasher,
    > Counter<T> for HyperLogLogCounter<'a, T, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    #[inline]
    fn add(&mut self, element: T) {
        let x = self.counter_array.hasher_builder.hash_one(element);
        let j = x & self.counter_array.num_registers_minus_1;
        let r = (x >> self.counter_array.log_2_num_registers | self.counter_array.sentinel_mask)
            .trailing_zeros() as HashResult;
        let register = j as usize;

        debug_assert!(r < (1 << self.counter_array.register_size) - 1);
        debug_assert!(register < self.counter_array.num_registers);

        let current_value = self.get_register(register);
        let candidate_value = r + 1;
        let new_value = std::cmp::max(
            current_value,
            candidate_value.try_into().unwrap_or_else(|_| {
                panic!(
                    "Should be able to convert {} from hash result type {} to word type {}.",
                    candidate_value,
                    std::any::type_name::<HashResult>(),
                    std::any::type_name::<W>()
                )
            }),
        );
        if current_value != new_value {
            self.set_register(register, new_value);
        }
    }

    #[inline]
    fn count(&self) -> u64 {
        self.estimate_count().round() as u64
    }

    #[inline]
    fn clear(&mut self) {
        for i in 0..self.counter_array.num_registers {
            self.set_register(i, W::ZERO);
        }
    }

    #[inline]
    fn merge(&mut self, other: &Self) {
        assert_eq!(
            self.counter_array.num_registers,
            other.counter_array.num_registers
        );
        assert_eq!(
            self.counter_array.register_size,
            other.counter_array.register_size
        );
        for i in 0..self.counter_array.num_registers {
            let current_value = self.get_register(i);
            let other_value = other.get_register(i);

            if other_value > current_value {
                self.set_register(i, other_value);
            }
        }
    }
}

impl<
        'a,
        T: Hash,
        W: Word + TryFrom<HashResult> + UpcastableInto<HashResult> + IntoAtomic,
        H: BuildHasher,
    > ApproximatedCounter<T> for HyperLogLogCounter<'a, T, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    #[inline]
    fn estimate_count(&self) -> f64 {
        let mut harmonic_mean = 0.0;
        let mut zeroes = 0;

        for i in 0..self.counter_array.num_registers {
            let value = self.get_register(i).upcast();
            if value == 0 {
                zeroes += 1;
            }
            harmonic_mean += 1.0 / (1 << value) as f64;
        }

        let mut estimate = self.counter_array.alpha_m_m / harmonic_mean;
        if zeroes != 0 && estimate < 2.5 * self.counter_array.num_registers as f64 {
            estimate = self.counter_array.num_registers as f64
                * (self.counter_array.num_registers as f64 / zeroes as f64).ln();
        }
        estimate
    }
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> PartialEq for HyperLogLogCounter<'a, T, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    fn eq(&self, other: &Self) -> bool {
        if self.counter_array.num_registers != other.counter_array.num_registers {
            return false;
        }
        if self.counter_array.register_size != other.counter_array.register_size {
            return false;
        }
        for i in 0..self.counter_array.num_registers {
            if self.get_register(i) != other.get_register(i) {
                return false;
            }
        }
        true
    }
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> Eq for HyperLogLogCounter<'a, T, W, H> where
    W::AtomicType: AtomicUnsignedInt + AsBytes
{
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> ToOwned for HyperLogLogCounter<'a, T, W, H> {
    type Owned = HyperLogLogCounter<'a, T, W, H>;

    fn to_owned(&self) -> Self::Owned {
        let mut c = HyperLogLogCounter {
            cached_bits: None,
            counter_array: self.counter_array,
            offset: self.offset,
            thread_helper: None,
        };
        unsafe {
            c.cache();
        }
        c
    }
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> CachableCounter
    for HyperLogLogCounter<'a, T, W, H>
{
    fn into_owned(mut self) -> <Self as ToOwned>::Owned
    where
        Self: Sized,
    {
        unsafe {
            self.cache();
        }
        self
    }
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> BitwiseCounter<T, W>
    for HyperLogLogCounter<'a, T, W, H>
{
    fn as_words(&self) -> &[W] {
        match &self.cached_bits {
            Some((bits, _)) => bits.as_slice(),
            None => {
                let num_words = self.counter_array.words_per_counter();
                let bits_offset = self.offset * self.counter_array.register_size;
                // Counters should be byte-aligned
                debug_assert!(bits_offset % 8 == 0);
                let byte_offset = bits_offset / 8;
                let num_bytes = num_words * W::BYTES;
                // We should copy whole words, not parts
                debug_assert!((num_bytes * 8) % W::BITS == 0);

                unsafe {
                    let pointer = (self.counter_array.bits.as_slice().as_ptr() as *const W)
                        .byte_add(byte_offset);
                    debug_assert!(pointer.is_aligned());

                    std::slice::from_raw_parts(pointer, num_words)
                }
            }
        }
    }

    unsafe fn as_mut_words_unsafe(&mut self) -> &mut [W] {
        match &mut self.cached_bits {
            Some((bits, _)) => bits.as_mut_slice(),
            None => {
                let num_words = self.counter_array.words_per_counter();
                let bits_offset = self.offset * self.counter_array.register_size;
                // Counters should be byte-aligned
                debug_assert!(bits_offset % 8 == 0);
                let byte_offset = bits_offset / 8;
                let num_bytes = num_words * W::BYTES;
                // We should copy whole words, not parts
                debug_assert!((num_bytes * 8) % W::BITS == 0);
                unsafe {
                    let pointer = (self.counter_array.bits.as_slice().as_ptr() as *mut W)
                        .byte_add(byte_offset);
                    debug_assert!(pointer.is_aligned());

                    std::slice::from_raw_parts_mut(pointer, num_words)
                }
            }
        }
    }

    unsafe fn merge_bitwise_unsafe(&mut self, other: &impl BitwiseCounter<T, W>) {
        let other = HyperLogLogCounter {
            counter_array: self.counter_array,
            offset: 0,
            thread_helper: None,
            cached_bits: Some((
                BitFieldVec::from_raw_parts(
                    Vec::from_iter(other.as_words().iter().cloned()),
                    self.counter_array.register_size,
                    self.counter_array.num_registers,
                ),
                false,
            )),
        };
        self.merge_unsafe(&other);
    }

    unsafe fn set_to_bitwise_unsafe(&mut self, other: &impl BitwiseCounter<T, W>) {
        let other = HyperLogLogCounter {
            counter_array: self.counter_array,
            offset: 0,
            thread_helper: None,
            cached_bits: Some((
                BitFieldVec::from_raw_parts(
                    Vec::from_iter(other.as_words().iter().cloned()),
                    self.counter_array.register_size,
                    self.counter_array.num_registers,
                ),
                false,
            )),
        };
        self.set_to(&other);
    }

    unsafe fn set_to_words_unsafe(&mut self, _words: &[W]) {
        todo!()
    }
}
