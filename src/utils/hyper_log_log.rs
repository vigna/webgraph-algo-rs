use crate::prelude::*;
use common_traits::*;
use std::{
    hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hash, Hasher},
    marker::PhantomData,
};
use sux::prelude::*;

pub struct HyperLogLogCounterArray<
    T,
    W: Word = usize,
    H: BuildHasher = BuildHasherDefault<DefaultHasher>,
> {
    /// The bits of the registers
    bits: UnsafeSyncCell<BitFieldVec<W>>,
    /// The number of registers per counter
    num_registers: u64,
    /// The number of registers per counter minus 1
    num_registers_minus_1: u64,
    /// the *log<sub>2</sub>* of the number of registers per counter
    log_2_num_registers: u64,
    /// The size in bits of each register
    register_size: u64,
    /// The size in bits of each counter
    counter_size: u64,
    /// The correct value for αm<sup>2</sup>
    alpha_m_m: f64,
    /// The mask OR'd with the output of the hash function so that the number of trailing zeroes is not
    /// too large of a value
    sentinel_mask: u64,
    /// The builder of the hashers
    hasher_builder: H,
    _phantom_data: PhantomData<T>,
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
        tmp / ((1usize << log_2_num_registers) as f64).sqrt()
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

impl<T> HyperLogLogCounterArray<T> {
    pub fn from_rsd(num_counters: usize, num_elements: usize, rsd: f64) -> Self {
        Self::from_log_2_num_registers(
            num_counters,
            num_elements,
            HyperLogLogCounterArray::log_2_number_of_registers(rsd),
        )
    }

    pub fn from_log_2_num_registers(
        num_counters: usize,
        num_elements: usize,
        log_2_num_registers: usize,
    ) -> Self {
        Self::from_hasher_builder(
            num_counters,
            num_elements,
            log_2_num_registers,
            BuildHasherDefault::default(),
        )
    }
}

impl<T, H: BuildHasher> HyperLogLogCounterArray<T, usize, H> {
    pub fn from_hasher_builder(
        num_counters: usize,
        num_elements: usize,
        log_2_num_registers: usize,
        hasher_builder: H,
    ) -> Self {
        let number_of_registers = 2.pow(log_2_num_registers);
        let register_size =
            HyperLogLogCounterArray::register_size_from_number_of_elements(num_elements);
        let sentinel_mask = 1 << (1 << register_size) - 2;
        let alpha = match log_2_num_registers {
            4 => 0.673,
            5 => 0.697,
            6 => 0.709,
            _ => 0.7213 / (1.0 + 1.079 / number_of_registers as f64),
        };

        Self {
            bits: UnsafeSyncCell::new(BitFieldVec::new(
                register_size,
                number_of_registers * num_counters,
            )),
            num_registers: number_of_registers.try_into().unwrap(),
            num_registers_minus_1: (number_of_registers - 1).try_into().unwrap(),
            log_2_num_registers: log_2_num_registers.try_into().unwrap(),
            register_size: register_size.try_into().unwrap(),
            counter_size: (register_size * number_of_registers).try_into().unwrap(),
            alpha_m_m: alpha * number_of_registers as f64 * number_of_registers as f64,
            sentinel_mask,
            hasher_builder,
            _phantom_data: PhantomData,
        }
    }
}

impl<T, W: Word, H: BuildHasher> HyperLogLogCounterArray<T, W, H> {
    #[inline(always)]
    pub fn get_counter(&self, index: usize) -> HyperLogLogCounter<T, W, H> {
        HyperLogLogCounter {
            counter_array: &self,
            offset: index * self.num_registers as usize,
            _phantom_data: PhantomData,
        }
    }
}

pub struct HyperLogLogCounter<'a, T, W: Word, H: BuildHasher> {
    counter_array: &'a HyperLogLogCounterArray<T, W, H>,
    offset: usize,
    _phantom_data: PhantomData<T>,
}

impl<'a, T: Hash, W: Word + UpcastableFrom<u32>, H: BuildHasher> Counter<T>
    for HyperLogLogCounter<'a, T, W, H>
{
    fn add(&mut self, element: T) {
        let mut hasher = self.counter_array.hasher_builder.build_hasher();
        element.hash(&mut hasher);

        let x = hasher.finish();
        let j = x & self.counter_array.num_registers_minus_1;
        let r = (x >> self.counter_array.log_2_num_registers | self.counter_array.sentinel_mask)
            .trailing_zeros();
        let register = self.offset + j as usize;

        debug_assert!(r < (1 << self.counter_array.register_size) - 1);

        let current_value = unsafe { self.counter_array.bits.as_mut_unsafe().get(register) };
        let candidate_value = r + 1;
        let new_value = std::cmp::max(current_value, candidate_value.upcast());
        unsafe {
            self.counter_array
                .bits
                .as_mut_unsafe()
                .set(register, new_value)
        }
    }

    fn count(&self) -> u64 {
        todo!()
    }

    fn clear(&mut self) {
        for i in 0..self.counter_array.num_registers {
            unsafe {
                self.counter_array
                    .bits
                    .as_mut_unsafe()
                    .set(self.offset + i as usize, W::ZERO)
            }
        }
    }
}
