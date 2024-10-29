use super::*;
use crate::{prelude::*, utils::MmapSlice};
use anyhow::{ensure, Context, Result};
use common_traits::{AsBytes, Atomic, AtomicUnsignedInt, IntoAtomic, Number, UpcastableInto};
use rayon::prelude::*;
use std::{
    f64::consts::LN_2,
    hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hash},
    marker::PhantomData,
    sync::atomic::Ordering,
};
use sux::{bits::*, traits::bit_field_slice::*};

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

/// Builder for [`HyperLogLogCounterArray`].
///
/// Create a builder with [`HyperLogLogCounterArrayBuilder::new`], edit parameters with
/// its methods, then call [`HyperLogLogCounterArrayBuilder::build`] on it to create
/// the [`HyperLogLogCounterArray`] as a [`Result`].
///
/// It assumes the counters are `W-aligned`.
///
/// ```
/// # use webgraph_algo::utils::HyperLogLogCounterArrayBuilder;
/// # use webgraph_algo::prelude::*;
/// # use anyhow::Result;
/// # fn main() -> Result<()> {
/// // Create a HyperLogLogCounterArray with 10 counters, each with
/// // 16 registers and an upper bound on the number of elements equal to 30
/// // and using a backend of usize.
/// // Type of the counter is usually inferred if the counter is used,
/// // otherwise it must be specified.
/// let mut counter_array = HyperLogLogCounterArrayBuilder::new()
///     .log_2_num_registers(6)
///     .num_elements_upper_bound(30)
///     .build(10)?;
/// counter_array.get_counter(0).add(42);
///
/// assert_eq!(counter_array.into_vec().len(), 10);
///
/// let counter_array = HyperLogLogCounterArrayBuilder::new()
///     .log_2_num_registers(6)
///     .num_elements_upper_bound(30)
///     .build::<usize>(10)?;
///
/// assert_eq!(counter_array.into_vec().len(), 10);
///
/// // The backend can also be changed to other unsigned types.
/// // Note that the type must be able to hold the result of the hash function.
/// let counter_array = HyperLogLogCounterArrayBuilder::new()
///     .log_2_num_registers(6)
///     .num_elements_upper_bound(30)
///     .word_type::<u64>()
///     .build::<usize>(10)?;
///
/// assert_eq!(counter_array.into_vec().len(), 10);
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct HyperLogLogCounterArrayBuilder<H: BuildHasher, W: Word + IntoAtomic> {
    log_2_num_registers: usize,
    num_elements: usize,
    mmap_options: TempMmapOptions,
    hasher_builder: H,
    word: PhantomData<W>,
}

impl HyperLogLogCounterArrayBuilder<BuildHasherDefault<DefaultHasher>, usize> {
    /// Creates a new builder for an [`HyperLogLogCounterArray`] with a default word type
    /// of [`usize`].
    pub fn new() -> Self {
        Self::new_with_word_type()
    }
}

impl<W: Word + IntoAtomic> HyperLogLogCounterArrayBuilder<BuildHasherDefault<DefaultHasher>, W> {
    /// Creates a new builder for an [`HyperLogLogCounterArray`] with a word type of `W`.
    pub fn new_with_word_type() -> Self {
        Self {
            log_2_num_registers: 4,
            num_elements: 1,
            hasher_builder: BuildHasherDefault::<DefaultHasher>::default(),
            mmap_options: TempMmapOptions::Default,
            word: PhantomData,
        }
    }
}

impl<H: BuildHasher, W: Word + IntoAtomic> HyperLogLogCounterArrayBuilder<H, W> {
    /// Sets the counters desired relative standard deviation.
    ///
    /// ## Note
    /// This is a high-level alternative to [`Self::log_2_num_registers`].
    /// Calling one after the other invalidates the work done by the first one.
    ///
    /// # Arguments
    /// * `rsd`: the relative standard deviation to be attained.
    pub fn rsd(self, rsd: f64) -> Self {
        self.log_2_num_registers(HyperLogLogCounterArray::log_2_number_of_registers(rsd))
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
    pub fn hasher_builder<H2: BuildHasher>(
        self,
        hasher_builder: H2,
    ) -> HyperLogLogCounterArrayBuilder<H2, W> {
        HyperLogLogCounterArrayBuilder {
            log_2_num_registers: self.log_2_num_registers,
            num_elements: self.num_elements,
            mmap_options: self.mmap_options,
            hasher_builder,
            word: PhantomData,
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

    /// Sets the word type to be used by the counters.
    pub fn word_type<W2: Word + IntoAtomic>(self) -> HyperLogLogCounterArrayBuilder<H, W2> {
        HyperLogLogCounterArrayBuilder {
            log_2_num_registers: self.log_2_num_registers,
            num_elements: self.num_elements,
            mmap_options: self.mmap_options,
            hasher_builder: self.hasher_builder,
            word: PhantomData,
        }
    }

    /// Builds the counter array with the specified len, consuming the builder.
    ///
    /// The type of objects the counters keep track of is defined here by `T`, but
    /// it is usually inferred by the compiler.
    ///
    /// # Arguments
    /// * `len`: the length of the counter array in counters.
    pub fn build<T>(self, len: usize) -> Result<HyperLogLogCounterArray<T, W, H>> {
        let num_counters = len;
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
                "should be able to convert {} from usize to the hash result type {}",
                number_of_registers - 1,
                std::any::type_name::<HashResult>()
            )
        });

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

        let required_words = counter_size_in_words * num_counters;
        let bits_vec =
            MmapSlice::from_closure(|| W::AtomicType::new(W::ZERO), required_words, mmap_options)
                .with_context(|| "Could not create bits for hyperloglog array as MmapSlice")?;
        let bits = unsafe {
            AtomicBitFieldVec::from_raw_parts(
                bits_vec,
                register_size,
                number_of_registers * num_counters,
            )
        };

        Ok(HyperLogLogCounterArray {
            bits,
            num_counters,
            num_registers: number_of_registers,
            num_registers_minus_1,
            log_2_num_registers,
            register_size,
            alpha_m_m: alpha * (number_of_registers as f64).powi(2),
            sentinel_mask,
            hasher_builder,
            msb_mask: msb,
            lsb_mask: lsb,
            words_per_counter: counter_size_in_words,
            _phantom_data: PhantomData,
        })
    }
}

impl<W: Word + IntoAtomic> Default
    for HyperLogLogCounterArrayBuilder<BuildHasherDefault<DefaultHasher>, W>
{
    fn default() -> Self {
        Self::new_with_word_type()
    }
}

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
    pub(super) bits: AtomicBitFieldVec<W, MmapSlice<W::AtomicType>>,
    /// The number of counters
    pub(super) num_counters: usize,
    /// The number of registers per counter
    pub(super) num_registers: usize,
    /// The number of registers per counter minus 1
    pub(super) num_registers_minus_1: HashResult,
    /// The *log<sub>2</sub>* of the number of registers per counter
    pub(super) log_2_num_registers: usize,
    /// The size in bits of each register
    pub(super) register_size: usize,
    /// The correct value for αm<sup>2</sup>
    pub(super) alpha_m_m: f64,
    /// The mask OR'd with the output of the hash function so that the number of trailing zeroes is not
    /// too large of a value
    pub(super) sentinel_mask: HashResult,
    /// The builder of the hashers
    pub(super) hasher_builder: H,
    /// A mask containing a one in the most significant bit of each register
    pub(super) msb_mask: BitFieldVec<W>,
    /// A mask containing a one in the least significant bit of each register
    pub(super) lsb_mask: BitFieldVec<W>,
    /// The number of words per counter
    pub(super) words_per_counter: usize,
    _phantom_data: PhantomData<T>,
}

impl HyperLogLogCounterArray<()> {
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
    /// Returns the number of words `W` per counter.
    #[inline(always)]
    pub fn words_per_counter(&self) -> usize {
        self.words_per_counter
    }

    /// Swaps the undelying bits with those of aother equivalent array.
    ///
    /// # Arguments
    /// * `other`: the array to swap bits with
    pub fn swap_with(&mut self, other: &mut Self) {
        assert_eq!(self.num_counters, other.num_counters);
        assert_eq!(self.num_registers, other.num_registers);
        assert_eq!(self.register_size, other.register_size);
        std::mem::swap(&mut self.bits, &mut other.bits);
    }

    /// Returns the register size.
    #[inline(always)]
    pub fn register_size(&self) -> usize {
        self.register_size
    }

    /// Returns the number of registers per counter.
    #[inline(always)]
    pub fn num_registers(&self) -> usize {
        self.num_registers
    }

    /// Returns the log₂ of the number of registers per counter.
    #[inline(always)]
    pub fn log_2_num_registers(&self) -> usize {
        self.log_2_num_registers
    }
}

impl<
        T: Sync + Hash,
        W: Word + IntoAtomic + UpcastableInto<u64> + TryFrom<u64>,
        H: BuildHasher + Sync,
    > HyperLogLogCounterArray<T, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
    for<'a> Self: HyperLogLogArray<'a, T, W>,
    for<'a, 'b> <Self as HyperLogLogArray<'a, T, W>>::Counter<'b>: Send,
{
    /// Creates a [`Vec`] where `v[i]` is the counter with index `i`.
    pub fn to_vec(&mut self) -> Vec<<Self as HyperLogLogArray<'_, T, W>>::Counter<'_>> {
        let mut vec = Vec::with_capacity(self.num_counters);
        (0..self.num_counters)
            .into_par_iter()
            .map(|i| unsafe { self.get_counter_from_shared(i) })
            .collect_into_vec(&mut vec);
        vec
    }
}

impl<
        'b,
        T: Hash + 'b,
        W: Word + IntoAtomic + UpcastableInto<u64> + TryFrom<u64> + 'b,
        H: BuildHasher + Clone + 'b,
    > HyperLogLogArray<'b, T, W> for HyperLogLogCounterArray<T, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    type Counter<'a> = HyperLogLogCounter<'a, 'b, T, W, H, &'a mut [W], &'a Self> where T: 'a, W: 'a, H: 'a;

    #[inline(always)]
    unsafe fn get_counter_from_shared(&self, index: usize) -> Self::Counter<'_> {
        assert!(index < self.num_counters);
        let mut ptr = self.bits.as_slice().as_ptr() as *mut W;
        ptr = ptr.add(self.words_per_counter * index);
        let bits = std::slice::from_raw_parts_mut(ptr, self.words_per_counter);
        HyperLogLogCounter {
            array: self,
            bits,
            thread_helper: None,
            _phantom_data: std::marker::PhantomData,
        }
    }

    #[inline(always)]
    fn get_thread_helper(&self) -> <Self::Counter<'_> as ThreadHelperCounter<'b>>::ThreadHelper {
        ThreadHelper {
            acc: Vec::with_capacity(self.words_per_counter),
            mask: Vec::with_capacity(self.words_per_counter),
        }
    }
}
