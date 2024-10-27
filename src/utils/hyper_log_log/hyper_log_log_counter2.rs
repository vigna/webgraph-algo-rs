use super::*;
use crate::prelude::*;
use common_traits::{IntoAtomic, UpcastableInto};
use std::hash::*;
use sux::{bits::BitFieldVec, traits::bit_field_slice::*};

/// Utility struct for parallel optimization.
pub struct ThreadHelper2<W: Word> {
    pub(super) acc: Vec<W>,
    pub(super) mask: Vec<W>,
}

pub struct HyperLogLogCounter2<
    'a,
    T,
    W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>,
    H: BuildHasher = BuildHasherDefault<DefaultHasher>,
    B = BitFieldVec<W, &'a mut [W]>,
> {
    pub(super) array: &'a HyperLogLogCounterArray<T, W, H>,
    pub(super) bits: B,
    pub(super) thread_helper: Option<&'a mut ThreadHelper2<W>>,
}

impl<
        'a,
        T: Hash,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>,
        H: BuildHasher,
        B: BitFieldSlice<W> + BitFieldSliceMut<W>,
    > HyperLogLogCounter2<'a, T, W, H, B>
{
    /// Sets a register of the counter to the specified new value.
    ///
    /// # Arguments
    /// * `index`: the index of the register to edit.
    /// * `new_value`: the new value to store in the register.
    #[inline(always)]
    fn set_register(&mut self, index: usize, new_value: W) {
        self.bits.set(index, new_value);
    }

    /// Gets the current value of the specified register.
    ///
    /// # Arguments
    /// * `index`: the index of the register to read.
    #[inline(always)]
    fn get_register(&self, index: usize) -> W {
        self.bits.get(index)
    }
}

impl<
        'a,
        T: Hash,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>,
        H: BuildHasher,
        B: BitFieldSlice<W> + BitFieldSliceMut<W>,
    > Counter<T> for HyperLogLogCounter2<'a, T, W, H, B>
{
    fn add(&mut self, element: T) {
        let x = self.array.hasher_builder.hash_one(element);
        let j = x & self.array.num_registers_minus_1;
        let r = (x >> self.array.log_2_num_registers | self.array.sentinel_mask).trailing_zeros()
            as HashResult;
        let register = j as usize;

        debug_assert!(r < (1 << self.array.register_size) - 1);
        debug_assert!(register < self.array.num_registers);

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

    fn clear(&mut self) {
        for i in 0..self.array.num_registers {
            self.set_register(i, W::ZERO);
        }
    }

    fn count(&self) -> u64 {
        self.estimate_count() as u64
    }

    fn merge(&mut self, other: &Self) {
        assert_eq!(self.array.num_registers, other.array.num_registers);
        assert_eq!(self.array.register_size, other.array.register_size);
        for i in 0..self.array.num_registers {
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
        W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>,
        H: BuildHasher,
        B: BitFieldSlice<W> + BitFieldSliceMut<W>,
    > ApproximatedCounter<T> for HyperLogLogCounter2<'a, T, W, H, B>
{
    fn estimate_count(&self) -> f64 {
        let mut harmonic_mean = 0.0;
        let mut zeroes = 0;

        for i in 0..self.array.num_registers {
            let value = self.get_register(i).upcast();
            if value == 0 {
                zeroes += 1;
            }
            harmonic_mean += 1.0 / (1 << value) as f64;
        }

        let mut estimate = self.array.alpha_m_m / harmonic_mean;
        if zeroes != 0 && estimate < 2.5 * self.array.num_registers as f64 {
            estimate = self.array.num_registers as f64
                * (self.array.num_registers as f64 / zeroes as f64).ln();
        }
        estimate
    }
}

impl<'a, T, W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>, H: BuildHasher>
    CachableCounter for HyperLogLogCounter2<'a, T, W, H, BitFieldVec<W, &'a mut [W]>>
{
    type OwnedCounter = HyperLogLogCounter2<'a, T, W, H, BitFieldVec<W, Vec<W>>>;

    fn get_copy(&self) -> Self::OwnedCounter {
        let v = Vec::from_iter(self.bits.iter());
        let bit_field = unsafe {
            BitFieldVec::from_raw_parts(v, self.array.register_size, self.array.num_registers)
        };
        Self::OwnedCounter {
            array: self.array,
            thread_helper: None,
            bits: bit_field,
        }
    }

    fn into_owned(self) -> Self::OwnedCounter
    where
        Self: Sized,
    {
        let (v, width, len) = self.bits.into_raw_parts();
        let v = v.to_owned();
        let bit_field = unsafe { BitFieldVec::from_raw_parts(v, width, len) };
        Self::OwnedCounter {
            array: self.array,
            thread_helper: self.thread_helper,
            bits: bit_field,
        }
    }

    fn copy_into_owned(&self, dst: &mut Self::OwnedCounter) {
        dst.set_to_bitwise(self);
    }
}

impl<
        'a,
        T,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>,
        H: BuildHasher,
        B: AsRef<[W]> + AsMut<[W]>,
    > BitwiseCounter<W> for HyperLogLogCounter2<'a, T, W, H, BitFieldVec<W, B>>
{
    #[inline(always)]
    fn as_words(&self) -> &[W] {
        self.bits.as_slice()
    }

    #[inline(always)]
    fn as_mut_words(&mut self) -> &mut [W] {
        self.bits.as_mut_slice()
    }

    fn merge_bitwise(&mut self, other: &impl BitwiseCounter<W>) {
        // The temporary vectors if no thread helper is used
        let mut acc_internal;
        let mut mask_internal;

        let num_words = self.array.words_per_counter();

        let msb_mask = self.array.msb_mask.as_slice();
        let lsb_mask = self.array.lsb_mask.as_slice();
        let x = self.bits.as_mut_slice();
        let y = other.as_words();
        let (acc, mask) = if let Some(helper) = &mut self.thread_helper {
            helper.acc.clear();
            helper.mask.clear();
            (&mut helper.acc, &mut helper.mask)
        } else {
            acc_internal = Vec::with_capacity(num_words);
            mask_internal = Vec::with_capacity(num_words);
            (&mut acc_internal, &mut mask_internal)
        };

        merge_hyperloglog_bitwise(
            x,
            y,
            msb_mask,
            lsb_mask,
            acc,
            mask,
            self.array.register_size,
        );
    }
}

impl<
        'a,
        T,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>,
        H: BuildHasher,
        B,
    > ThreadHelperCounter<'a> for HyperLogLogCounter2<'a, T, W, H, B>
{
    type ThreadHelper = ThreadHelper2<W>;

    fn use_thread_helper(&mut self, helper: &'a mut Self::ThreadHelper) {
        self.thread_helper = Some(helper)
    }

    fn remove_thread_helper(&mut self) {
        self.thread_helper.take();
    }
}

impl<
        'a,
        T,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>,
        H: BuildHasher,
        B: AsRef<[W]>,
    > PartialEq for HyperLogLogCounter2<'a, T, W, H, BitFieldVec<W, B>>
{
    fn eq(&self, other: &Self) -> bool {
        self.bits.as_slice() == other.bits.as_slice()
    }
}

impl<
        'a,
        T,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + TryFrom<u64>,
        H: BuildHasher,
        B: AsRef<[W]>,
    > Eq for HyperLogLogCounter2<'a, T, W, H, BitFieldVec<W, B>>
{
}
