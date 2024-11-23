use super::*;
use crate::{
    prelude::*,
    utils::{DefaultCounter, JenkinsHasherBuilder, MmapSlice},
};
use anyhow::{ensure, Context, Result};
use common_traits::{CastableFrom, CastableInto, Number, UpcastableInto};
use std::hash::*;
use std::{borrow::Borrow, f64::consts::LN_2};
use sux::{
    bits::BitFieldVec,
    traits::{BitFieldSliceMut, Word},
};

#[derive(Debug)]
pub struct HyperLogLog<T, W> {
    build_hasher: JenkinsHasherBuilder,
    register_size: usize,
    num_registers_minus_1: HashResult,
    log_2_num_registers: usize,
    sentinel_mask: HashResult,
    num_registers: usize,
    pub(super) words_per_counter: usize,
    alpha_m_m: f64,
    msb_mask: Box<[W]>,
    lsb_mask: Box<[W]>,
    _marker: std::marker::PhantomData<T>,
}

impl<T, W: Clone> Clone for HyperLogLog<T, W> {
    fn clone(&self) -> Self {
        Self {
            build_hasher: self.build_hasher.clone(),
            register_size: self.register_size,
            num_registers_minus_1: self.num_registers_minus_1,
            log_2_num_registers: self.log_2_num_registers,
            sentinel_mask: self.sentinel_mask,
            num_registers: self.num_registers,
            words_per_counter: self.words_per_counter,
            alpha_m_m: self.alpha_m_m,
            msb_mask: self.msb_mask.clone(),
            lsb_mask: self.lsb_mask.clone(),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<T, W: Word> HyperLogLog<T, W> {
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

    pub fn new_array(
        &self,
        len: usize,
        mmap_options: TempMmapOptions,
    ) -> Result<HyperLogLogArray<T, W>> {
        let bits = MmapSlice::from_default(len * self.words_per_counter, mmap_options)
            .with_context(|| "Could not create CounterArray with mmap")?;
        Ok(HyperLogLogArray {
            backend: bits,
            len,
            logic: self.clone(),
        })
    }
}

pub struct HyperLogLogHelper<W> {
    acc: Vec<W>,
    mask: Vec<W>,
}

impl<T: Hash, W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>> CounterLogic
    for HyperLogLog<T, W>
{
    type Item = T;
    type Backend = [W];
    type Counter<'a> = DefaultCounter<Self, Box<[W]>> where T: 'a, W: 'a;

    fn new_counter(&self) -> Self::Counter<'_> {
        Self::Counter {
            logic: self.clone(), // TODO: avoid clone
            backend: vec![W::ZERO; self.words_per_counter].into_boxed_slice(),
        }
    }

    fn add(&self, mut counter: impl AsMut<Self::Backend>, element: impl Borrow<T>) {
        let mut counter = counter.as_mut();
        let x = self.build_hasher.hash_one(element.borrow());
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

    /*    fn words_per_counter(&self) -> usize {
        self.words_per_counter
    }*/
}

impl<T: Hash, W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>> MergeCounterLogic
    for HyperLogLog<T, W>
{
    type Helper = HyperLogLogHelper<W>;

    fn new_helper(&self) -> Self::Helper {
        HyperLogLogHelper {
            acc: vec![W::ZERO; self.words_per_counter].into(),
            mask: vec![W::ZERO; self.words_per_counter].into(),
        }
    }

    fn merge_with_helper(
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

#[derive(Debug, Clone)]
pub struct HyperLogLogBuilder<W = usize> {
    log_2_num_registers: usize,
    num_elements: usize,
    seed: u64,
    _marker: std::marker::PhantomData<W>,
}

impl HyperLogLogBuilder<usize> {
    /// Creates a new builder for an [`HyperLogLog`] with a default word type
    /// of [`usize`].
    #[inline(always)]
    pub fn new() -> Self {
        Self::new_with_word_type()
    }
}

impl<W> HyperLogLogBuilder<W> {
    /// Creates a new builder for an [`HyperLogLog`] with a word type of `W`.
    pub fn new_with_word_type() -> Self {
        Self {
            log_2_num_registers: 4,
            num_elements: 1,
            seed: 0,
            _marker: std::marker::PhantomData,
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

impl<W: Word> HyperLogLogBuilder<W> {
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

    pub fn seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// Sets the word type to be used by the counters.
    pub fn word_type<W2: Word>(self) -> HyperLogLogBuilder<W2> {
        HyperLogLogBuilder {
            log_2_num_registers: self.log_2_num_registers,
            num_elements: self.num_elements,
            seed: self.seed,
            _marker: std::marker::PhantomData,
        }
    }

    /// Builds the counter logic.
    ///
    /// The type of objects the counters keep track of is defined here by `T`, but
    /// it is usually inferred by the compiler.
    pub fn build_logic<T>(&self) -> Result<HyperLogLog<T, W>> {
        let log_2_num_registers = self.log_2_num_registers;
        let num_elements = self.num_elements;

        // This ensures counters are at least 16-bit-aligned.
        ensure!(
            log_2_num_registers >= 4,
            "the logarithm of the number of registers per counter should be at least 4. Got {}",
            log_2_num_registers
        );

        let number_of_registers = 1 << log_2_num_registers;
        let register_size = HyperLogLog::register_size_from_number_of_elements(num_elements);
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

        Ok(HyperLogLog {
            num_registers: number_of_registers,
            num_registers_minus_1,
            log_2_num_registers,
            register_size,
            alpha_m_m: alpha * (number_of_registers as f64).powi(2),
            sentinel_mask,
            build_hasher: JenkinsHasherBuilder::new(self.seed),
            msb_mask: msb.as_slice().into(),
            lsb_mask: lsb.as_slice().into(),
            words_per_counter: counter_size_in_words,
            _marker: std::marker::PhantomData,
        })
    }
}

impl<W, H> std::fmt::Display for HyperLogLog<W, H> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
