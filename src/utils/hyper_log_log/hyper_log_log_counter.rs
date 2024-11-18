use super::*;
use crate::prelude::*;
use common_traits::{CastableFrom, CastableInto, IntoAtomic, UpcastableInto};
use std::hash::*;
use sux::{bits::BitFieldVec, traits::bit_field_slice::*};

/// Utility struct for parallel optimization.
#[derive(Debug, Clone)]
pub struct ThreadHelper<W: Word> {
    pub(super) acc: Vec<W>,
    pub(super) mask: Vec<W>,
}

/// Concretized view of an HyperLogLogCounter stored in a [`HyperLogLogCounterArray`].
///
/// This stores minimal information as a reference to the original array as an
/// `&'a HyperLogLogCounterArray<T, W, H>` or as a copy of the relevant information
/// stored in an [`OwnedArray`](`OwnedArray`)[^note].
///
/// Two versions of this counter are provided:
/// * A [`BitFieldVec`]-based implementation that provides optimized register operations at the
///   cost of a bigger memory footprint.
/// * A [`Vec`]-based implementation that is lighter on the memory but carries less information
///   and provides less optimized register-based operations.
///
/// [^note]: This structure is for internal use only and should only be used for type annotations.
#[derive(Debug)]
pub struct HyperLogLogCounter<'a, 'b, T, W: Word, H, B, A> {
    pub(super) array: A,
    pub(super) bits: B,
    pub(super) thread_helper: Option<&'b mut ThreadHelper<W>>,
    pub(super) _phantom_data: std::marker::PhantomData<&'a (T, H)>,
}

/// Internal structure storing owned information from an [`HyperLogLogCounterArray`] used by
/// the owned version of [`HyperLogLogCounter`].
///
/// <div class="warning">
///
/// This structure is for internal use onlt and should only be used for type annotations.
///
/// </div>
#[derive(Debug, Clone)]
pub struct OwnedArray<W: Word, H: BuildHasher> {
    build_hasher: H,
    register_size: usize,
    num_registers_minus_1: HashResult,
    log_2_num_registers: usize,
    sentinel_mask: HashResult,
    num_registers: usize,
    words_per_counter: usize,
    alpha_m_m: f64,
    msb_mask: Box<[W]>,
    lsb_mask: Box<[W]>,
}

impl<T, W: Word + IntoAtomic, H: BuildHasher + Clone> From<&HyperLogLogCounterArray<T, W, H>>
    for OwnedArray<W, H>
{
    fn from(value: &HyperLogLogCounterArray<T, W, H>) -> Self {
        OwnedArray {
            build_hasher: value.hasher_builder.clone(),
            register_size: value.register_size,
            num_registers_minus_1: value.num_registers_minus_1,
            log_2_num_registers: value.log_2_num_registers,
            sentinel_mask: value.sentinel_mask,
            num_registers: value.num_registers,
            words_per_counter: value.words_per_counter,
            alpha_m_m: value.alpha_m_m,
            msb_mask: value.msb_mask.as_slice().into(),
            lsb_mask: value.lsb_mask.as_slice().into(),
        }
    }
}

/// Internal trait for handling both owned and borrowed [`HyperLogLogCounterArray`].
trait ArrayInfo<W: Word, H: BuildHasher> {
    fn register_size(&self) -> usize;

    fn hasher_builder(&self) -> &H;

    fn num_registers_minus_1(&self) -> HashResult;

    fn log_2_num_registers(&self) -> usize;

    fn sentinel_mask(&self) -> HashResult;

    fn num_registers(&self) -> usize;

    fn alpha_m_m(&self) -> f64;

    fn msb_mask(&self) -> &[W];

    fn lsb_mask(&self) -> &[W];

    fn words_per_counter(&self) -> usize;
}

impl<T, W: Word + IntoAtomic, H: BuildHasher + Clone> ArrayInfo<W, H>
    for &HyperLogLogCounterArray<T, W, H>
{
    #[inline(always)]
    fn alpha_m_m(&self) -> f64 {
        self.alpha_m_m
    }

    #[inline(always)]
    fn hasher_builder(&self) -> &H {
        &self.hasher_builder
    }

    #[inline(always)]
    fn log_2_num_registers(&self) -> usize {
        self.log_2_num_registers
    }

    #[inline(always)]
    fn num_registers(&self) -> usize {
        self.num_registers
    }

    #[inline(always)]
    fn num_registers_minus_1(&self) -> HashResult {
        self.num_registers_minus_1
    }

    #[inline(always)]
    fn register_size(&self) -> usize {
        self.register_size
    }

    #[inline(always)]
    fn sentinel_mask(&self) -> HashResult {
        self.sentinel_mask
    }

    #[inline(always)]
    fn words_per_counter(&self) -> usize {
        self.words_per_counter
    }

    #[inline(always)]
    fn msb_mask(&self) -> &[W] {
        self.msb_mask.as_slice()
    }

    #[inline(always)]
    fn lsb_mask(&self) -> &[W] {
        self.lsb_mask.as_slice()
    }
}

impl<W: Word, H: BuildHasher> ArrayInfo<W, H> for OwnedArray<W, H> {
    #[inline(always)]
    fn alpha_m_m(&self) -> f64 {
        self.alpha_m_m
    }

    #[inline(always)]
    fn hasher_builder(&self) -> &H {
        &self.build_hasher
    }

    #[inline(always)]
    fn log_2_num_registers(&self) -> usize {
        self.log_2_num_registers
    }

    #[inline(always)]
    fn num_registers(&self) -> usize {
        self.num_registers
    }

    #[inline(always)]
    fn num_registers_minus_1(&self) -> HashResult {
        self.num_registers_minus_1
    }

    #[inline(always)]
    fn register_size(&self) -> usize {
        self.register_size
    }

    #[inline(always)]
    fn sentinel_mask(&self) -> HashResult {
        self.sentinel_mask
    }

    #[inline(always)]
    fn words_per_counter(&self) -> usize {
        self.words_per_counter
    }

    #[inline(always)]
    fn msb_mask(&self) -> &[W] {
        &self.msb_mask
    }

    #[inline(always)]
    fn lsb_mask(&self) -> &[W] {
        &self.lsb_mask
    }
}

/// Internal trait to handle register-based operations on all provided backends
/// for [`HyperLogLogCounter`].
trait RegisterEdit<W> {
    /// Sets a register of the counter to the specified new value.
    ///
    /// # Arguments
    /// * `index`: the index of the register to edit.
    /// * `new_value`: the new value to store in the register.
    fn set_register(&mut self, index: usize, new_value: W);

    /// Gets the current value of the specified register.
    ///
    /// # Arguments
    /// * `index`: the index of the register to read.
    fn get_register(&self, index: usize) -> W;
}

impl<'a, 'b, T: Hash, W: Word, H: BuildHasher, B: AsRef<[W]> + AsMut<[W]>, A: ArrayInfo<W, H>>
    RegisterEdit<W> for HyperLogLogCounter<'a, 'b, T, W, H, BitFieldVec<W, B>, A>
{
    #[inline(always)]
    fn set_register(&mut self, index: usize, new_value: W) {
        self.bits.set(index, new_value);
    }

    #[inline(always)]
    fn get_register(&self, index: usize) -> W {
        self.bits.get(index)
    }
}

impl<'a, 'b, T: Hash, W: Word, H: BuildHasher, A: ArrayInfo<W, H>> RegisterEdit<W>
    for HyperLogLogCounter<'a, 'b, T, W, H, Box<[W]>, A>
{
    #[inline(always)]
    fn get_register(&self, index: usize) -> W {
        let bit_width = self.array.register_size();
        let mask = W::MAX >> (W::BITS - bit_width);
        let pos = index * bit_width;
        let word_index = pos / W::BITS;
        let bit_index = pos % W::BITS;
        let bits = self.bits.as_ref();

        if bit_index + bit_width <= W::BITS {
            (unsafe { *bits.get_unchecked(word_index) } >> bit_index) & mask
        } else {
            (unsafe { *bits.get_unchecked(word_index) } >> bit_index
                | unsafe { *bits.get_unchecked(word_index + 1) } << (W::BITS - bit_index))
                & mask
        }
    }

    #[inline(always)]
    fn set_register(&mut self, index: usize, new_value: W) {
        let bit_width = self.array.register_size();
        let mask = W::MAX >> (W::BITS - bit_width);
        let pos = index * bit_width;
        let word_index = pos / W::BITS;
        let bit_index = pos % W::BITS;
        let bits = self.bits.as_mut();

        if bit_index + bit_width <= W::BITS {
            let mut word = unsafe { *bits.get_unchecked_mut(word_index) };
            word &= !(mask << bit_index);
            word |= new_value << bit_index;
            unsafe { *bits.get_unchecked_mut(word_index) = word };
        } else {
            let mut word = unsafe { *bits.get_unchecked_mut(word_index) };
            word &= (W::ONE << bit_index) - W::ONE;
            word |= new_value << bit_index;
            unsafe { *bits.get_unchecked_mut(word_index) = word };

            let mut word = unsafe { *bits.get_unchecked_mut(word_index + 1) };
            word &= !(mask >> (W::BITS - bit_index));
            word |= new_value >> (W::BITS - bit_index);
            unsafe { *bits.get_unchecked_mut(word_index + 1) = word };
        }
    }
}

impl<'a, 'b, T: Hash, W: Word, H: BuildHasher, A: ArrayInfo<W, H>> RegisterEdit<W>
    for HyperLogLogCounter<'a, 'b, T, W, H, &'a mut [W], A>
{
    #[inline(always)]
    fn get_register(&self, index: usize) -> W {
        let bit_width = self.array.register_size();
        let mask = W::MAX >> (W::BITS - bit_width);
        let pos = index * bit_width;
        let word_index = pos / W::BITS;
        let bit_index = pos % W::BITS;
        let bits = &self.bits;

        if bit_index + bit_width <= W::BITS {
            (unsafe { *bits.get_unchecked(word_index) } >> bit_index) & mask
        } else {
            (unsafe { *bits.get_unchecked(word_index) } >> bit_index
                | unsafe { *bits.get_unchecked(word_index + 1) } << (W::BITS - bit_index))
                & mask
        }
    }

    #[inline(always)]
    fn set_register(&mut self, index: usize, new_value: W) {
        let bit_width = self.array.register_size();
        let mask = W::MAX >> (W::BITS - bit_width);
        let pos = index * bit_width;
        let word_index = pos / W::BITS;
        let bit_index = pos % W::BITS;
        let bits = &mut self.bits;

        if bit_index + bit_width <= W::BITS {
            let mut word = unsafe { *bits.get_unchecked_mut(word_index) };
            word &= !(mask << bit_index);
            word |= new_value << bit_index;
            unsafe { *bits.get_unchecked_mut(word_index) = word };
        } else {
            let mut word = unsafe { *bits.get_unchecked_mut(word_index) };
            word &= (W::ONE << bit_index) - W::ONE;
            word |= new_value << bit_index;
            unsafe { *bits.get_unchecked_mut(word_index) = word };

            let mut word = unsafe { *bits.get_unchecked_mut(word_index + 1) };
            word &= !(mask >> (W::BITS - bit_index));
            word |= new_value >> (W::BITS - bit_index);
            unsafe { *bits.get_unchecked_mut(word_index + 1) = word };
        }
    }
}

impl<
        'a,
        'b,
        T: Hash,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + CastableFrom<HashResult>,
        H: BuildHasher,
        B: AsRef<[W]> + AsMut<[W]>,
        A: ArrayInfo<W, H>,
    > Counter<T> for HyperLogLogCounter<'a, 'b, T, W, H, B, A>
where
    Self: RegisterEdit<W>,
{
    fn add(&mut self, element: T) {
        let x = self.array.hasher_builder().hash_one(element);
        let j = x & self.array.num_registers_minus_1();
        let r = (x >> self.array.log_2_num_registers() | self.array.sentinel_mask())
            .trailing_zeros() as HashResult;
        let register = j as usize;

        debug_assert!(r < (1 << self.array.register_size()) - 1);
        debug_assert!(register < self.array.num_registers());

        let current_value = self.get_register(register);
        let candidate_value = r + 1;
        let new_value = std::cmp::max(current_value, candidate_value.cast());
        if current_value != new_value {
            self.set_register(register, new_value);
        }
    }

    fn clear(&mut self) {
        for i in 0..self.array.num_registers() {
            self.set_register(i, W::ZERO);
        }
    }

    fn count(&self) -> f64 {
        let mut harmonic_mean = 0.0;
        let mut zeroes = 0;
        let array = &self.array;

        for i in 0..array.num_registers() {
            let value = self.get_register(i).upcast();
            if value == 0 {
                zeroes += 1;
            }
            harmonic_mean += 1.0 / (1 << value) as f64;
        }

        let mut estimate = array.alpha_m_m() / harmonic_mean;
        if zeroes != 0 && estimate < 2.5 * array.num_registers() as f64 {
            estimate =
                array.num_registers() as f64 * (array.num_registers() as f64 / zeroes as f64).ln();
        }
        estimate
    }

    fn set_to(&mut self, other: &Self) {
        self.bits.as_mut().copy_from_slice(other.bits.as_ref());
    }
}

impl<
        'a,
        'b,
        T: Hash,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + CastableFrom<HashResult>,
        H: BuildHasher,
        B: AsRef<[W]> + AsMut<[W]>,
        A: ArrayInfo<W, H>,
    > MergeableCounter<T> for HyperLogLogCounter<'a, 'b, T, W, H, B, A>
where
    Self: RegisterEdit<W>,
{
    fn merge(&mut self, other: &Self) {
        let mut acc_internal;
        let mut mask_internal;

        let array = &self.array;
        let num_words = array.words_per_counter();

        let msb_mask = array.msb_mask();
        let lsb_mask = array.lsb_mask();
        let x = self.bits.as_mut();
        let y = other.bits.as_ref();
        let (acc, mask) = if let Some(helper) = &mut self.thread_helper {
            helper.acc.clear();
            helper.mask.clear();
            (&mut helper.acc, &mut helper.mask)
        } else {
            acc_internal = Vec::with_capacity(num_words);
            mask_internal = Vec::with_capacity(num_words);
            (&mut acc_internal, &mut mask_internal)
        };

        merge_hyperloglog_bitwise(x, y, msb_mask, lsb_mask, acc, mask, array.register_size());
    }
}

impl<'a, 'b, T, W: Word, H, B: AsMut<[W]>, A> HyperLogLogCounter<'a, 'b, T, W, H, B, A> {
    /// Sets the contents of `self` to the contents of `other`.
    pub fn set_to<B2: AsRef<[W]>, A2>(
        &mut self,
        other: &HyperLogLogCounter<'_, '_, T, W, H, B2, A2>,
    ) {
        self.bits.as_mut().copy_from_slice(other.bits.as_ref())
    }
}

impl<'a, 'b, T, W: Word + IntoAtomic, H: BuildHasher, B, A: ArrayInfo<W, H>>
    ThreadHelperCounter<'b, ThreadHelper<W>> for HyperLogLogCounter<'a, 'b, T, W, H, B, A>
{
    #[inline(always)]
    fn use_thread_helper(&mut self, helper: &'b mut ThreadHelper<W>) {
        self.thread_helper = Some(helper)
    }

    #[inline(always)]
    fn remove_thread_helper(&mut self) {
        self.thread_helper.take();
    }
}

impl<'a, 'b, T, W: Word + IntoAtomic, H: BuildHasher, B: AsRef<[W]>, A: ArrayInfo<W, H>> PartialEq
    for HyperLogLogCounter<'a, 'b, T, W, H, BitFieldVec<W, B>, A>
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.bits.as_slice() == other.bits.as_slice()
    }
}

impl<'a, 'b, T, W: Word + IntoAtomic, H: BuildHasher, B: AsRef<[W]>, A: ArrayInfo<W, H>> Eq
    for HyperLogLogCounter<'a, 'b, T, W, H, BitFieldVec<W, B>, A>
{
}

impl<'a, 'b, T, W: Word + IntoAtomic, H: BuildHasher, A: ArrayInfo<W, H>> PartialEq
    for HyperLogLogCounter<'a, 'b, T, W, H, Box<[W]>, A>
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.bits.as_ref() == other.bits.as_ref()
    }
}

impl<'a, 'b, T, W: Word + IntoAtomic, H: BuildHasher, A: ArrayInfo<W, H>> Eq
    for HyperLogLogCounter<'a, 'b, T, W, H, Box<[W]>, A>
{
}

impl<'a, 'b, T, W: Word + IntoAtomic, H: BuildHasher, A: ArrayInfo<W, H>> PartialEq
    for HyperLogLogCounter<'a, 'b, T, W, H, &'a mut [W], A>
{
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.bits == other.bits
    }
}

impl<'a, 'b, T, W: Word + IntoAtomic, H: BuildHasher, A: ArrayInfo<W, H>> Eq
    for HyperLogLogCounter<'a, 'b, T, W, H, &'a mut [W], A>
{
}
