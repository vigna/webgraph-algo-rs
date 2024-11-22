use super::*;
use crate::prelude::*;
use anyhow::ensure;
use common_traits::CastableFrom;
use common_traits::CastableInto;
use common_traits::IntoAtomic;
use common_traits::Number;
use common_traits::UpcastableFrom;
use common_traits::UpcastableInto;
use std::f64::consts::LN_2;
use std::{
    fmt::{Display, Formatter},
    hash::*,
    marker::PhantomData,
};
use sux::{bits::BitFieldVec, traits::bit_field_slice::*};

/*/// Concretized view of an HyperLogLogCounter stored in a [`HyperLogLog`].
///
/// This stores minimal information as a reference to the original array as an
/// `&'a HyperLogLog<T, W, H>` or as a copy of the relevant information
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
pub struct HyperLogLogCounter<'a, T, W: Word, H, B, A> {
    pub(super) array: A,
    pub(super) bits: B,
    pub(super) _phantom_data: std::marker::PhantomData<&'a (W, T, H)>,
}*/
/*
/// Internal structure storing owned information from an [`HyperLogLog`] used by
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

impl<T, W: Word + IntoAtomic, H: BuildHasher + Clone> From<&HyperLogLog<T, W, H>>
    for OwnedArray<W, H>
{
    fn from(value: &HyperLogLog<T, W, H>) -> Self {
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
}*/
/*
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
*/

#[derive(Debug, Clone)]
pub struct HyperLogLog<W, H> {
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

impl HyperLogLog<(), ()> {
    /// Returns the logarithm of the number of registers per counter that are necessary to attain a
    /// given relative stadard deviation.
    ///
    /// # Arguments
    /// * `rsd`: the relative standard deviation to be attained.
    pub fn log_2_number_of_registers(rsd: f64) -> usize {
        ((1.106 / rsd).pow(2.0)).log2().ceil() as usize
    }

    /// Returns the relative standard deviation corresponding to a given number of registers per counter.
    ///
    /// # Arguments
    /// * `log_2_num_registers`: the logarithm of the number of registers per counter.
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
    /// * `n`: an upper bound on the number of distinct elements.
    pub fn register_size_from_number_of_elements(n: usize) -> usize {
        std::cmp::max(5, (((n as f64).ln() / LN_2) / LN_2).ln().ceil() as usize)
    }
}

impl<W: Word, H> HyperLogLog<W, H> {
    #[inline(always)]
    fn get_register(&self, counter: impl AsRef<[W]>, index: usize) -> W {
        let counter = counter.as_ref();
        let bit_width = self.register_size;
        let mask = W::MAX >> (W::BITS - bit_width);
        let pos = index * bit_width;
        let word_index = pos / W::BITS;
        let bit_index = pos % W::BITS;

        if bit_index + bit_width <= W::BITS {
            (unsafe { *counter.get_unchecked(word_index) } >> bit_index) & mask
        } else {
            (unsafe { *counter.get_unchecked(word_index) } >> bit_index
                | unsafe { *counter.get_unchecked(word_index + 1) } << (W::BITS - bit_index))
                & mask
        }
    }

    #[inline(always)]
    fn set_register(&self, mut counter: impl AsMut<[W]>, index: usize, new_value: W) {
        let counter = counter.as_mut();
        let bit_width = self.register_size;
        let mask = W::MAX >> (W::BITS - bit_width);
        let pos = index * bit_width;
        let word_index = pos / W::BITS;
        let bit_index = pos % W::BITS;

        if bit_index + bit_width <= W::BITS {
            let mut word = unsafe { *counter.get_unchecked_mut(word_index) };
            word &= !(mask << bit_index);
            word |= new_value << bit_index;
            unsafe { *counter.get_unchecked_mut(word_index) = word };
        } else {
            let mut word = unsafe { *counter.get_unchecked_mut(word_index) };
            word &= (W::ONE << bit_index) - W::ONE;
            word |= new_value << bit_index;
            unsafe { *counter.get_unchecked_mut(word_index) = word };

            let mut word = unsafe { *counter.get_unchecked_mut(word_index + 1) };
            word &= !(mask >> (W::BITS - bit_index));
            word |= new_value >> (W::BITS - bit_index);
            unsafe { *counter.get_unchecked_mut(word_index + 1) = word };
        }
    }
}
pub struct HyperLogLogHelper<W> {
    acc: Vec<W>,
    mask: Vec<W>,
}

impl<T: Hash, W: Word, H: BuildHasher> CounterLogic<T> for HyperLogLog<W, H>
where
    u64: UpcastableFrom<W>,
    W: CastableFrom<u64>,
{
    type Backend = [W];

    fn add(&self, mut counter: impl AsMut<[W]>, element: T) {
        let mut counter = counter.as_mut();
        let x = self.build_hasher.hash_one(element);
        let j = x & self.num_registers_minus_1;
        let r = (x >> self.log_2_num_registers | self.sentinel_mask).trailing_zeros() as HashResult;
        let register = j as usize;

        debug_assert!(r < (1 << self.register_size) - 1);
        debug_assert!(register < self.num_registers);

        let current_value = self.get_register(&mut counter, register);
        let candidate_value = r + 1;
        let new_value = std::cmp::max(current_value, candidate_value.cast());
        if current_value != new_value {
            self.set_register(counter, register, new_value);
        }
    }

    fn count(&self, counter: impl AsRef<[W]>) -> f64 {
        let counter = counter.as_ref();
        let mut harmonic_mean = 0.0;
        let mut zeroes = 0;

        for i in 0..self.num_registers {
            let value: u64 = self.get_register(counter, i).upcast();
            if value == 0 {
                zeroes += 1;
            }
            harmonic_mean += 1.0 / (1 << value) as f64;
        }

        let mut estimate = self.alpha_m_m / harmonic_mean;
        if zeroes != 0 && estimate < 2.5 * self.num_registers as f64 {
            estimate = self.num_registers as f64 * (self.num_registers as f64 / zeroes as f64).ln();
        }
        estimate
    }

    fn clear(&self, mut counter: impl AsMut<[W]>) {
        counter.as_mut().fill(W::ZERO);
    }

    fn set_to(&self, mut dst: impl AsMut<[W]>, src: impl AsRef<[W]>) {
        debug_assert_eq!(dst.as_mut().len(), src.as_ref().len());
        dst.as_mut().copy_from_slice(src.as_ref());
    }

    fn words_per_counter(&self) -> usize {
        self.words_per_counter
    }
}

impl<T: Hash, W: Word, H: BuildHasher> MergeCounterLogic<T> for HyperLogLog<W, H>
where
    u64: UpcastableFrom<W>,
    W: CastableFrom<u64>,
{
    type Helper = HyperLogLogHelper<W>;

    fn new_helper(&self) -> Self::Helper {
        HyperLogLogHelper {
            acc: vec![W::ZERO; self.words_per_counter].into(),
            mask: vec![W::ZERO; self.words_per_counter].into(),
        }
    }

    fn merge_into_with_helper(
        &self,
        dst: impl AsMut<[W]>,
        src: impl AsRef<[W]>,
        helper: &mut Self::Helper,
    ) {
        merge_hyperloglog_bitwise(
            dst,
            src,
            self.msb_mask.as_ref(),
            self.lsb_mask.as_ref(),
            &mut helper.acc,
            &mut helper.mask,
            self.register_size,
        );
    }
}
pub struct HyperLogLogBuilder<H = BuildHasherDefault<DefaultHasher>, W = usize> {
    log_2_num_registers: usize,
    num_elements: usize,
    mmap_options: TempMmapOptions,
    hasher_builder: H,
    _marker: PhantomData<W>,
}

impl<H: Default, W> HyperLogLogBuilder<H, W> {
    /// Creates a new builder for an [`HyperLogLog`] with a word type of `W`.
    pub fn new() -> Self {
        Self {
            log_2_num_registers: 4,
            num_elements: 1,
            hasher_builder: H::default(),
            mmap_options: TempMmapOptions::Default,
            _marker: PhantomData,
        }
    }
}

fn min_alignment(bits: usize) -> String {
    if bits % 128 == 0 {
        "u128"
    } else if bits % 64 == 0 {
        "u64"
    } else if bits % 32 == 0 {
        "u32"
    } else if bits % 16 == 0 {
        "u16"
    } else {
        "u8"
    }
    .to_string()
}

impl<H: BuildHasher + Clone, W: Word + IntoAtomic> HyperLogLogBuilder<H, W> {
    /// Sets the counters desired relative standard deviation.
    ///
    /// ## Note
    /// This is a high-level alternative to [`Self::log_2_num_registers`].
    /// Calling one after the other invalidates the work done by the first one.
    ///
    /// # Arguments
    /// * `rsd`: the relative standard deviation to be attained.
    pub fn rsd(self, rsd: f64) -> Self {
        self.log_2_num_registers(HyperLogLog::log_2_number_of_registers(rsd))
    }

    /// Sets the log₂*m* number of registers for the array of counters.
    ///
    /// ## Note
    /// This is a low-level alternative to [`Self::rsd`].
    /// Calling one after the other invalidates the work done by the first one.
    ///
    /// # Arguments
    /// * `log_2_num_registers`: the logarithm of the number of registers per counter.
    pub fn log_2_num_registers(mut self, log_2_num_registers: usize) -> Self {
        self.log_2_num_registers = log_2_num_registers;
        self
    }

    /// Sets the upper bound on the number of distinct elements to be added to the
    /// counters.
    ///
    /// # Arguments
    /// * `num_elements`: an upper bound on the number of distinct elements.
    pub fn num_elements_upper_bound(mut self, num_elements: usize) -> Self {
        self.num_elements = num_elements;
        self
    }

    /// Sets the hasher builder to be used by the counters.
    ///
    /// # Arguments
    /// * `hasher_builder`: the builder of the hasher used by the array that implements
    ///   [`BuildHasher`].
    pub fn hasher_builder<H2: BuildHasher + Clone>(
        self,
        hasher_builder: H2,
    ) -> HyperLogLogBuilder<H2, W> {
        HyperLogLogBuilder {
            log_2_num_registers: self.log_2_num_registers,
            num_elements: self.num_elements,
            mmap_options: self.mmap_options,
            hasher_builder,
            _marker: PhantomData,
        }
    }

    /// Sets the memory options for the couters.
    ///
    /// # Arguments
    /// * `options`: the memory options for the backend of the counter array.
    pub fn mem_options(mut self, options: TempMmapOptions) -> Self {
        self.mmap_options = options;
        self
    }

    /// Returns the register size in bits, given an upper bound on the number of distinct elements.
    ///
    /// # Arguments
    /// * `n`: an upper bound on the number of distinct elements.
    pub fn register_size_from_number_of_elements(n: usize) -> usize {
        std::cmp::max(5, (((n as f64).ln() / LN_2) / LN_2).ln().ceil() as usize)
    }

    /// Builds the counter array with the specified len, consuming the builder.
    ///
    /// The type of objects the counters keep track of is defined here by `T`, but
    /// it is usually inferred by the compiler.
    ///
    /// # Arguments
    /// * `len`: the length of the counter array in counters.
    pub fn build(self) -> anyhow::Result<HyperLogLog<W, H>> {
        let log_2_num_registers = self.log_2_num_registers;
        let num_elements = self.num_elements;
        let hasher_builder = self.hasher_builder;
        let mmap_options = self.mmap_options;

        // This ensures counters are at least 16-bit-aligned.
        ensure!(
            log_2_num_registers >= 4,
            "the logarithm of the number of registers per counter should be at least 4. Got {}",
            log_2_num_registers
        );

        let number_of_registers = 1 << log_2_num_registers;
        let register_size = Self::register_size_from_number_of_elements(num_elements);
        let sentinel_mask = 1 << ((1 << register_size) - 2);
        let alpha = match log_2_num_registers {
            4 => 0.673,
            5 => 0.697,
            6 => 0.709,
            _ => 0.7213 / (1.0 + 1.079 / number_of_registers as f64),
        };
        let num_registers_minus_1 = (number_of_registers - 1) as HashResult;

        let counter_size_in_bits = number_of_registers * register_size;

        // This ensures counters are always aligned to W
        ensure!(
            counter_size_in_bits % W::BITS == 0,
            "W should allow counters to be aligned. Use {} or smaller words",
            min_alignment(counter_size_in_bits)
        );
        let counter_size_in_words = counter_size_in_bits / W::BITS;

        let mut msb = BitFieldVec::new(register_size, number_of_registers);
        let mut lsb = BitFieldVec::new(register_size, number_of_registers);
        let msb_w = W::ONE << (register_size - 1);
        let lsb_w = W::ONE;
        for i in 0..number_of_registers {
            msb.set(i, msb_w);
            lsb.set(i, lsb_w);
        }

        /*let required_words = counter_size_in_words * num_counters;
                let bits =
                    MmapSlice::from_closure(|| W::AtomicType::new(W::ZERO), required_words, mmap_options)
                        .with_context(|| "Could not create bits for hyperloglog array as MmapSlice")?;
        */
        Ok(HyperLogLog {
            num_registers: number_of_registers,
            num_registers_minus_1,
            log_2_num_registers,
            register_size,
            alpha_m_m: alpha * (number_of_registers as f64).powi(2),
            sentinel_mask,
            build_hasher: hasher_builder,
            msb_mask: msb.into_raw_parts().0.into_boxed_slice(),
            lsb_mask: lsb.into_raw_parts().0.into_boxed_slice(),
            words_per_counter: counter_size_in_words,
        })
    }
}

impl<W, H> Display for HyperLogLog<W, H> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,

            "Relative standard deviation: {}% ({} registers/counter, {} bits/register, {} bytes/counter)",
            100.0 * HyperLogLog::relative_standard_deviation(self.log_2_num_registers),
            self.num_registers,
            self.register_size,
            (self.num_registers * self.register_size) / 8
        )
    }
}

pub struct DefaultCounter<T, L: CounterLogic<T>, B: AsRef<L::Backend> + AsMut<L::Backend>, W> {
    logic: L,
    backend: B,
    _marker: PhantomData<(T, W)>,
}

impl<T, L: CounterLogic<T>, B: AsRef<L::Backend> + AsMut<L::Backend>, W: Word> Counter<T>
    for DefaultCounter<T, L, B, W>
{
    fn add(&mut self, element: T) {
        self.logic.add(&mut self.backend, element);
    }

    fn count(&self) -> f64 {
        self.logic.count(&self.backend)
    }

    fn clear(&mut self) {
        self.logic.clear(&mut self.backend);
    }

    fn set_to(&mut self, other: &Self) {
        self.logic.set_to(&mut self.backend, &other.backend);
    }
}

impl<T, L: MergeCounterLogic<T>, B: AsRef<L::Backend> + AsMut<L::Backend>, W: Word> MergeCounter<T>
    for DefaultCounter<T, L, B, W>
{
    fn merge(&mut self, other: &Self) {
        self.logic.merge_into(&mut self.backend, &other.backend);
    }
}
