use crate::{prelude::*, utils::closure_vec};
use common_traits::*;
use rayon::prelude::*;
use std::{
    hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hash},
    marker::PhantomData,
    sync::atomic::Ordering,
};
use sux::prelude::*;

type HashResult = u64;

/// An abstracted array of [`HyperLogLogCounter`].
///
/// This array is created using an [`AtomicBitFieldVec`] as a backend in order to avoid
/// wasting memory.
///
/// Individual counters can be accessed with the [`Self::get_counter`] method or concretized
/// as a [`Vec`] of [`HyperLogLogCounter`].
pub struct HyperLogLogCounterArray<
    T,
    W: Word + IntoAtomic = usize,
    H: BuildHasher = BuildHasherDefault<DefaultHasher>,
> {
    /// The bits of the registers
    bits: AtomicBitFieldVec<W>,
    /// The number of counters
    num_counters: usize,
    /// The number of registers per counter
    num_registers: usize,
    /// The number of registers per counter minus 1
    num_registers_minus_1: HashResult,
    /// the *log<sub>2</sub>* of the number of registers per counter
    log_2_num_registers: usize,
    /// The size in bits of each register
    register_size: usize,
    /// The correct value for αm<sup>2</sup>
    alpha_m_m: f64,
    /// The mask OR'd with the output of the hash function so that the number of trailing zeroes is not
    /// too large of a value
    sentinel_mask: HashResult,
    /// The builder of the hashers
    hasher_builder: H,
    /// The number of counters needed for a chunk to be aliged with `W`
    chunk_size: usize,
    /// The number of counters needed for a chunk to be aliged with `W` minus 1
    chunk_size_minus_1: usize,
    /// A mask containing a one in the most significant bit of each register
    msb_mask: BitFieldVec<W>,
    /// A mask containing a one in the least significant bit of each register
    lsb_mask: BitFieldVec<W>,
    _phantom_data: PhantomData<T>,
}

impl<T> HyperLogLogCounterArray<T> {
    /// Creates an [`HyperLogLogCounterArray`] that tries to attain the specified
    /// relative standard deviation.
    ///
    /// # Arguments
    /// - `num_counters`: the number of counters to create in the array.
    /// - `num_elements`: an upper bound on the number of distinct elements.
    /// - `rsd`: the relative standard deviation to be attained.
    pub fn with_rsd(num_counters: usize, num_elements: usize, rsd: f64) -> Self {
        Self::with_log_2_num_registers(
            num_counters,
            num_elements,
            HyperLogLogCounterArray::log_2_number_of_registers(rsd),
        )
    }

    /// Creates an [`HyperLogLogCounterArray`] with the specified log₂*m*
    /// number of registers.
    ///
    /// # Arguments
    /// - `num_counters`: the number of counters to create in the array.
    /// - `num_elements`: an upper bound on the number of distinct elements.
    /// - `log_2_num_registers`: the logarithm of the number of registers per counter.
    pub fn with_log_2_num_registers(
        num_counters: usize,
        num_elements: usize,
        log_2_num_registers: usize,
    ) -> Self {
        Self::with_hasher_builder(
            num_counters,
            num_elements,
            log_2_num_registers,
            BuildHasherDefault::default(),
        )
    }
}

impl<T, W: Word + IntoAtomic, H: BuildHasher> HyperLogLogCounterArray<T, W, H>
where
    W::AtomicType: AtomicUnsignedInt,
{
    /// Creates an [`HyperLogLogCounterArray`] with the specified *log<sub>2</sub>m*
    /// number of registers and hasher builder.
    ///
    /// # Arguments
    /// - `num_counters`: the number of counters to create in the array.
    /// - `num_elements`: an upper bound on the number of distinct elements.
    /// - `log_2_num_registers`: the logarithm of the number of registers per counter.
    /// - `hasher_builder`: the builder of the hasher used by the array that implements
    ///   [`BuildHasher`].
    pub fn with_hasher_builder(
        num_counters: usize,
        num_elements: usize,
        log_2_num_registers: usize,
        hasher_builder: H,
    ) -> Self {
        // This ensures counters are at least 16-bit-aligned.
        assert!(
            log_2_num_registers >= 4,
            "the logarithm of the number of registers per counter should be at least 4. Got {}",
            log_2_num_registers
        );

        let number_of_registers = 1 << log_2_num_registers;
        let register_size =
            HyperLogLogCounterArray::register_size_from_number_of_elements(num_elements);
        let sentinel_mask = 1 << ((1 << register_size) - 2);
        let alpha = match log_2_num_registers {
            4 => 0.673,
            5 => 0.697,
            6 => 0.709,
            _ => 0.7213 / (1.0 + 1.079 / number_of_registers as f64),
        };
        let num_registers_minus_1 = (number_of_registers - 1).try_into().unwrap_or_else(|_| {
            panic!(
                "should be able to convert {} from usize to the hash result type",
                number_of_registers - 1
            )
        });

        let counter_size_in_bits = number_of_registers * register_size;
        let mut chunk_size = 1;
        while (counter_size_in_bits * chunk_size) % W::BITS != 0 {
            chunk_size += 1;
        }

        let mut msb = BitFieldVec::new(register_size, number_of_registers);
        let mut lsb = BitFieldVec::new(register_size, number_of_registers);
        let msb_w = W::ONE << (register_size - 1);
        let lsb_w = W::ONE;
        for i in 0..number_of_registers {
            msb.set(i, msb_w);
            lsb.set(i, lsb_w);
        }

        let mut required_words = std::cmp::max(
            1,
            (number_of_registers * num_counters * register_size + W::BITS - 1) / W::BITS,
        );
        if chunk_size > 1 {
            // This allows cache to copy non-aligned words without having to check whether the backend
            // is long enough.
            required_words += 1;
        }
        let bits_vec = closure_vec(|| W::AtomicType::new(W::ZERO), required_words);
        debug_assert!(
            number_of_registers * num_counters * register_size <= bits_vec.len() * W::BITS
        );
        let bits = unsafe {
            AtomicBitFieldVec::from_raw_parts(
                bits_vec,
                register_size,
                number_of_registers * num_counters,
            )
        };

        Self {
            bits,
            num_counters,
            num_registers: number_of_registers,
            num_registers_minus_1,
            log_2_num_registers,
            register_size,
            alpha_m_m: alpha * (number_of_registers as f64).pow(2.0),
            sentinel_mask,
            hasher_builder,
            chunk_size,
            chunk_size_minus_1: chunk_size - 1,
            msb_mask: msb,
            lsb_mask: lsb,
            _phantom_data: PhantomData,
        }
    }
}

impl HyperLogLogCounterArray<()> {
    /// Returns the logarithm of the number of registers per counter that are necessary to attain a
    /// giver relative stadard deviation.
    ///
    /// # Arguments
    /// - `rsd`: the relative standard deviation to be attained.
    pub fn log_2_number_of_registers(rsd: f64) -> usize {
        ((1.106 / rsd).pow(2.0)).log2().ceil() as usize
    }

    /// Returns the relative standard deviation corresponding to a given number of registers per counter.
    ///
    /// # Arguments
    /// - `log_2_num_registers`: the logarithm of the number of registers per counter.
    pub fn relative_standard_deviation(log_2_num_registers: usize) -> f64 {
        let tmp = match log_2_num_registers {
            4 => 1.106,
            5 => 1.070,
            6 => 1.054,
            7 => 1.046,
            _ => 1.04,
        };
        tmp / ((1 << log_2_num_registers) as f64).sqrt()
    }

    /// Returns the register size in bits, given an upper bound on the number of distinct elements.
    ///
    /// # Arguments
    /// - `n`: an upper bound on the number of distinct elements.
    pub fn register_size_from_number_of_elements(n: usize) -> usize {
        std::cmp::max(
            5,
            (((n as f64).ln() / 2.0.ln()) / 2.0.ln()).ln().ceil() as usize,
        )
    }
}

impl<T, W: Word + IntoAtomic, H: BuildHasher> HyperLogLogCounterArray<T, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    /// Resets all counters by writing zeroes in all registers.
    pub fn clear(&mut self) {
        self.bits.reset_atomic(Ordering::Relaxed)
    }
}

impl<T, W: Word + IntoAtomic, H: BuildHasher> HyperLogLogCounterArray<T, W, H> {
    /// Returns the concretized [`HyperLogLogCounter`] with the specified index.
    ///
    /// # Arguments
    /// - `index`: the index of the counter to concretize.
    #[inline(always)]
    pub fn get_counter(&self, index: usize) -> HyperLogLogCounter<T, W, H> {
        HyperLogLogCounter {
            counter_array: self,
            offset: index * self.num_registers,
            cached_bits: None,
        }
    }

    /// Returns the number of words `W` per counter.
    #[inline(always)]
    pub fn words_per_counter(&self) -> usize {
        self.msb_mask.as_slice().len()
    }
}

impl<T: Sync, W: Word + IntoAtomic, H: BuildHasher + Sync> HyperLogLogCounterArray<T, W, H> {
    /// Creates a [`Vec`] where `v[i]` is the [`HyperLogLogCounter`] with index `i`.
    pub fn into_vec(&self) -> Vec<HyperLogLogCounter<T, W, H>> {
        let mut vec = Vec::with_capacity(self.num_counters);
        (0..self.num_counters)
            .into_par_iter()
            .map(|i| self.get_counter(i))
            .collect_into_vec(&mut vec);
        vec
    }
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
    counter_array: &'a HyperLogLogCounterArray<T, W, H>,
    /// The offset of the first register of the counter.
    offset: usize,
    /// The cached counter bits. Remeinder bits are to be considered noise and not used.
    cached_bits: Option<BitFieldVec<W>>,
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> HyperLogLogCounter<'a, T, W, H> {
    /// Returns the index of the current counter
    #[inline(always)]
    pub fn counter_index(&self) -> usize {
        self.offset / self.counter_array.num_registers
    }

    /// Returns the chunk this counter belongs to.
    #[inline(always)]
    pub fn chunk_index(&self) -> usize {
        self.counter_index() / self.counter_array.chunk_size
    }

    /// Returns whether the counter is the last of a chunk and needs to be updated without overlapping
    /// the next. This is used by [`Self::merge_unsafe`].
    #[inline(always)]
    pub fn is_last_of_chunk(&self) -> bool {
        self.counter_index() % self.counter_array.chunk_size
            == self.counter_array.chunk_size_minus_1
    }
}

impl<'a, T, W: Word + IntoAtomic, H: BuildHasher> HyperLogLogCounter<'a, T, W, H> {
    /// Performs a multiple precision subtraction, leaving the result in the first operand.
    /// The operands MUST have the same length.
    ///
    /// # Arguments
    /// - `x`: the first operand. This will contain the final result.
    /// - `y`: the second operand that will be subtracted from `x`.
    #[inline(always)]
    fn subtract(x: &mut [W], y: &[W]) {
        debug_assert_eq!(x.len(), y.len());
        let mut borrow = false;

        for (x_word, &y_word) in x.iter_mut().zip(y.iter()) {
            let mut signed_x_word = x_word.to_signed();
            let signed_y_word = y_word.to_signed();
            if !borrow {
                borrow = Self::borrow_check(signed_x_word, signed_y_word);
            } else {
                signed_x_word = signed_x_word.wrapping_sub(W::SignedInt::ZERO);
                if signed_x_word != W::SignedInt::ZERO {
                    borrow = Self::borrow_check(signed_x_word, signed_y_word);
                }
            }
            signed_x_word = signed_x_word.wrapping_sub(signed_y_word);
            *x_word = signed_x_word.to_unsigned();
        }
    }

    /// Returns the result of an unsigned strict comparison
    #[inline(always)]
    fn borrow_check<N: Number>(x: N, y: N) -> bool {
        (x < y) ^ (x < N::ZERO) ^ (y < N::ZERO)
    }

    /// Merges `other` into `self` inplace using words instead of registers.
    ///
    /// `other` is not modified but `self` is.
    ///
    /// # Arguments
    /// - `other`: the counter to merge into `self`.
    ///
    /// # Safety
    ///
    /// Calling this method on two counters from the same chunk from two
    /// different threads at the same time is [undefined behavior].
    ///
    /// Calling this method while reading (ie. with [`Self::cache`] on the same counter from
    /// another instance) or writing (ie. with [`Self::commit_changes`]) from the same memory
    /// zone in the backend [`HyperLogLogCounterArray`] is [undefined behavior].
    ///
    /// Calling this method on the same counters at the same time in
    /// different directions without first calling [`Self::cache`] as
    /// is shown below is [undefined behavior]:
    /// ```no_run
    /// # use rayon::join;
    /// # use webgraph_algo::utils::HyperLogLogCounterArray;
    /// # use webgraph_algo::prelude::Counter;
    /// let counters = HyperLogLogCounterArray::with_rsd(2, 10, 0.1);
    /// let mut c1 = counters.get_counter(0);
    /// let mut c2 = counters.get_counter(1);
    /// let c1_shared = counters.get_counter(0);
    /// let c2_shared = counters.get_counter(1);
    /// # counters.get_counter(0).add(0);
    ///
    /// // This is undefined behavior
    /// join(|| unsafe {c1.merge_unsafe(&c2_shared)}, || unsafe {c2.merge_unsafe(&c1_shared)});
    /// ```
    ///
    /// On the other hand, once the counter is cached it is fine:
    ///
    /// ```
    /// # use rayon::join;
    /// # use webgraph_algo::utils::HyperLogLogCounterArray;
    /// # use webgraph_algo::prelude::Counter;
    /// let counters = HyperLogLogCounterArray::with_rsd(2, 10, 0.1);
    /// let mut c1 = counters.get_counter(0);
    /// let mut c2 = counters.get_counter(1);
    /// let c1_shared = counters.get_counter(0);
    /// let c2_shared = counters.get_counter(1);
    /// # counters.get_counter(0).add(0);
    ///
    /// unsafe {
    ///     c1.cache();
    ///     c2.cache();
    /// }
    ///
    /// // This is fine
    /// join(|| unsafe {c1.merge_unsafe(&c2_shared)}, || unsafe {c2.merge_unsafe(&c1_shared)});
    /// ```
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn merge_unsafe(&mut self, other: &Self) {
        // Whether to call Self::commit_changes at the end because
        // the counter was cached here.
        // This is sound as the mut ref prevents other references from
        // existing.
        let mut commit = false;
        // The temporary vector containing the local copy of the other counter
        let mut y_vec;

        let num_words = self.counter_array.words_per_counter();
        let register_size_minus_1 = self.counter_array.register_size - 1;
        let shift_register_size_minus_1 = register_size_minus_1.wrapping_neg() & 0b11111;

        let msb_mask = self.counter_array.msb_mask.as_slice();
        let lsb_mask = self.counter_array.lsb_mask.as_slice();
        let x = match &mut self.cached_bits {
            Some(bits) => bits.as_mut_slice(),
            None => {
                let bits_offset = self.offset * self.counter_array.register_size;
                // Counters should be byte-aligned
                debug_assert!(bits_offset % 8 == 0);
                let byte_offset = bits_offset / 8;
                let num_bytes = num_words * W::BYTES;
                // We should copy whole words, not parts
                debug_assert!((num_bytes * 8) % W::BITS == 0);

                let pointer =
                    (other.counter_array.bits.as_slice().as_ptr() as *mut W).byte_add(byte_offset);

                if pointer.is_aligned() {
                    std::slice::from_raw_parts_mut(pointer, num_words)
                } else {
                    self.cache();
                    commit = true;
                    self.cached_bits
                        .as_mut()
                        .expect("Counter should be cached")
                        .as_mut_slice()
                }
            }
        };
        let y = match &other.cached_bits {
            Some(bits) => bits.as_slice(),
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

                if pointer.is_aligned() {
                    std::slice::from_raw_parts(pointer, num_words)
                } else {
                    y_vec = Vec::with_capacity(num_words);
                    std::ptr::copy_nonoverlapping(
                        pointer as *const u8,
                        y_vec.as_mut_ptr() as *mut u8,
                        num_bytes,
                    );
                    y_vec.set_len(num_words);

                    y_vec.as_slice()
                }
            }
        };

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
        let mut acc = Vec::from_iter(
            y.iter()
                .zip(msb_mask.iter())
                .map(|(&y_word, &msb_word)| y_word | msb_word),
        );

        // We load x & !H_r into mask as temporary storage.
        let mut mask = Vec::from_iter(
            x.iter()
                .zip(msb_mask.iter())
                .map(|(x_word, &msb_word)| x_word & !msb_word),
        );

        // We subtract x & !H_r, using mask as temporary storage
        Self::subtract(&mut acc, &mask);

        // We OR with y ^ x, XOR with (y | !x), and finally AND with H_r.
        acc.iter_mut()
            .zip(x.iter())
            .zip(y.iter())
            .zip(msb_mask.iter())
            .for_each(|(((acc_word, x_word), &y_word), &msb_word)| {
                *acc_word = ((*acc_word | (y_word ^ x_word)) ^ (y_word | !x_word)) & msb_word
            });

        // We shift by register_size - 1 places and put the result into mask.
        mask[0..num_words - 1]
            .iter_mut()
            .zip(acc[0..num_words - 1].iter())
            .zip(acc[1..].iter())
            .zip(msb_mask.iter())
            .rev()
            .for_each(|(((mask_word, &acc_word), &next_acc_word), &msb_word)| {
                // W is always unsigned so the shift is always with a 0
                *mask_word = (acc_word >> register_size_minus_1)
                    | (next_acc_word << shift_register_size_minus_1)
                    | msb_word
            });
        mask[num_words - 1] =
            (acc[num_words - 1] >> register_size_minus_1) | msb_mask[num_words - 1];

        // We subtract L_r from mask.
        Self::subtract(&mut mask, lsb_mask);

        // We OR with H_r and XOR with the accumulator.
        mask.iter_mut()
            .zip(msb_mask.iter())
            .zip(acc.iter())
            .for_each(|((mask_word, &msb_word), acc_word)| {
                *mask_word = (*mask_word | msb_word) ^ acc_word
            });

        // Finally, we use mask to select the right bits from x and y and store the result.
        x.iter_mut()
            .zip(y.iter())
            .zip(mask.iter())
            .for_each(|((x_word, &y_word), mask_word)| *x_word ^= (*x_word ^ y_word) & mask_word);

        if commit {
            self.commit_changes();
        }
    }

    /// Commit changes to this counter to the backend [`HyperLogLogCounterArray`].
    ///
    /// Calling this method on a counter whose registers aren't cached with [`Self::cache`]
    /// will result in a panic.
    ///
    /// # Safety
    ///
    /// Calling this method while reading from the same memory zone in the backend
    /// [`HyperLogLogCounterArray`] (ie. with [`Self::cache`] on the same counter from
    /// another instance) is [undefined behavior].
    /// ```no_run
    /// # use rayon::join;
    /// # use webgraph_algo::utils::HyperLogLogCounterArray;
    /// # use webgraph_algo::prelude::Counter;
    /// let counters = HyperLogLogCounterArray::with_rsd(2, 10, 0.1);
    /// let mut c1 = counters.get_counter(0);
    /// let mut c1_copy = counters.get_counter(0);
    ///
    /// unsafe { c1.cache() };
    /// c1.add(0);
    ///
    /// // This is undefined behavior
    /// join(|| unsafe {c1.commit_changes()}, || unsafe {c1_copy.cache()});
    /// ```
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn commit_changes(&mut self) {
        let cached = self
            .cached_bits
            .as_ref()
            .expect("counter should be cached first")
            .as_slice();
        let bits_to_write = self.counter_array.num_registers * self.counter_array.register_size;
        debug_assert!((W::BITS * cached.len()) - bits_to_write < W::BITS);
        debug_assert!(bits_to_write % 8 == 0);
        debug_assert_eq!(cached.len(), self.counter_array.words_per_counter());
        let bytes_to_write = bits_to_write / 8;

        let bits_offset = self.offset * self.counter_array.register_size;
        debug_assert!(bits_offset % 8 == 0);
        let byte_offset = bits_offset / 8;

        let pointer =
            (self.counter_array.bits.as_slice().as_ptr() as *mut u8).byte_add(byte_offset);

        std::ptr::copy_nonoverlapping(cached.as_ptr() as *const u8, pointer, bytes_to_write);

        self.cached_bits = None;
    }

    /// Cache the counter registers.
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
    /// ```no_run
    /// # use rayon::join;
    /// # use webgraph_algo::utils::HyperLogLogCounterArray;
    /// # use webgraph_algo::prelude::Counter;
    /// let counters = HyperLogLogCounterArray::with_rsd(2, 10, 0.1);
    /// let mut c1 = counters.get_counter(0);
    /// let mut c1_copy = counters.get_counter(0);
    ///
    /// unsafe { c1.cache() };
    /// c1.add(0);
    ///
    /// // This is undefined behavior
    /// join(|| unsafe {c1.commit_changes()}, || unsafe {c1_copy.cache()});
    /// ```
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn cache(&mut self) {
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

        self.cached_bits = Some(BitFieldVec::from_raw_parts(
            v,
            self.counter_array.register_size,
            self.counter_array.num_registers,
        ));
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
    /// - `index`: the index of the register to edit.
    /// - `new_value`: the new value to store in the register.
    #[inline(always)]
    fn set_register(&mut self, index: usize, new_value: W) {
        match &mut self.cached_bits {
            Some(bits) => bits.set(index, new_value),
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
    /// - `index`: the index of the register to read.
    #[inline(always)]
    fn get_register(&self, index: usize) -> W {
        match &self.cached_bits {
            Some(bits) => bits.get(index),
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
        W: Word + UpcastableFrom<HashResult> + UpcastableInto<HashResult> + IntoAtomic,
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
        let new_value = std::cmp::max(current_value, candidate_value.upcast());
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
        W: Word + UpcastableFrom<HashResult> + UpcastableInto<HashResult> + IntoAtomic,
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
            let float_value = value as f64;
            harmonic_mean += 2.0.pow(-float_value);
        }

        let mut estimate = self.counter_array.alpha_m_m / harmonic_mean;
        if zeroes != 0 && estimate < 2.5 * self.counter_array.num_registers as f64 {
            estimate = self.counter_array.num_registers as f64
                * (self.counter_array.num_registers as f64 / zeroes as f64).ln();
        }
        estimate
    }
}
