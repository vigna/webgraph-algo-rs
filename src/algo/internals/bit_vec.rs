use std::{ops::Index, sync::atomic::*};

const BITS: usize = usize::BITS as usize;

pub struct AtomicBitVec<T = Vec<AtomicUsize>> {
    data: T,
    len: usize,
}

macro_rules! panic_if_out_of_bounds {
    ($index: expr, $len: expr) => {
        if $index >= $len {
            panic!("Bit index out of bounds: {} >= {}", $index, $len)
        }
    };
}

impl AtomicBitVec<Vec<AtomicUsize>> {
    pub fn new(len: usize) -> Self {
        let n_of_words = (len + BITS - 1) / BITS;
        Self {
            data: (0..n_of_words).map(|_| AtomicUsize::new(0)).collect(),
            len,
        }
    }
}

impl<B: AsRef<[AtomicUsize]>> AtomicBitVec<B> {
    pub fn get(&self, index: usize, order: Ordering) -> bool {
        panic_if_out_of_bounds!(index, self.len);
        unsafe { self.get_unchecked(index, order) }
    }

    pub fn set(&self, index: usize, value: bool, order: Ordering) {
        panic_if_out_of_bounds!(index, self.len);
        unsafe { self.set_unchecked(index, value, order) }
    }

    pub fn swap(&self, index: usize, value: bool, order: Ordering) -> bool {
        panic_if_out_of_bounds!(index, self.len);
        unsafe { self.swap_unchecked(index, value, order) }
    }

    unsafe fn get_unchecked(&self, index: usize, order: Ordering) -> bool {
        let word_index = index / BITS;
        let data: &[AtomicUsize] = self.data.as_ref();
        let word = data.get_unchecked(word_index).load(order);
        (word >> (index % BITS)) & 1 != 0
    }

    unsafe fn set_unchecked(&self, index: usize, value: bool, order: Ordering) {
        let word_index = index / BITS;
        let bit_index = index % BITS;
        let data: &[AtomicUsize] = self.data.as_ref();

        if value {
            data.get_unchecked(word_index)
                .fetch_or(1 << bit_index, order);
        } else {
            data.get_unchecked(word_index)
                .fetch_and(!(1 << bit_index), order);
        }
    }

    unsafe fn swap_unchecked(&self, index: usize, value: bool, order: Ordering) -> bool {
        let word_index = index / BITS;
        let bit_index = index % BITS;
        let data: &[AtomicUsize] = self.data.as_ref();

        let old_value = if value {
            data.get_unchecked(word_index)
                .fetch_or(1 << bit_index, order)
        } else {
            data.get_unchecked(word_index)
                .fetch_and(!(1 << bit_index), order)
        };

        (old_value >> (bit_index)) & 1 != 0
    }
}

impl<B: AsRef<[AtomicUsize]>> Index<usize> for AtomicBitVec<B> {
    type Output = bool;

    fn index(&self, index: usize) -> &Self::Output {
        match self.get(index, Ordering::Relaxed) {
            false => &false,
            true => &true,
        }
    }
}
