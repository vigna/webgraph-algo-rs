use super::*;
use crate::utils::DefaultCounter;
use crate::{prelude::*, utils::MmapSlice};
use common_traits::{CastableFrom, UpcastableInto};
use std::cell::UnsafeCell;
use std::hash::*;
use sux::traits::Word;

pub(super) struct UnsafeSyncCell<T>(UnsafeCell<T>);

impl<T> UnsafeSyncCell<T> {
    #[inline(always)]
    fn new(value: T) -> Self {
        Self(UnsafeCell::new(value))
    }
}

impl<T: Default> Default for UnsafeSyncCell<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new(T::default())
    }
}

unsafe impl<T: Sync> Sync for UnsafeSyncCell<T> {}

impl<T> std::ops::Deref for UnsafeSyncCell<T> {
    type Target = UnsafeCell<T>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub struct HyperLogLogArray<T, W: Word> {
    pub(super) logic: HyperLogLog<T, W>,
    pub(super) backend: MmapSlice<UnsafeSyncCell<W>>,
    pub(super) len: usize,
}

impl<T, W: Word> HyperLogLogArray<T, W> {
    ///Returns the number of elements in the array, also referred to as its ‘length’.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the array contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[allow(dead_code)]
    pub(crate) fn as_slice(&self) -> &[W] {
        let len = self.backend.len();
        let ptr = UnsafeCell::raw_get(self.backend.as_slice() as *const [_] as *const _);
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }
}

impl<T: Hash, W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>>
    CounterArray<HyperLogLog<T, W>> for HyperLogLogArray<T, W>
{
    type Counter<'a> = DefaultCounter<HyperLogLog<T, W>, &'a mut [W]> where Self: 'a; // TODO: avoid mut
    type CounterMut<'a> = DefaultCounter<HyperLogLog<T, W>, &'a mut [W]> where Self: 'a;

    fn get_backend(
        &self,
        index: usize,
    ) -> impl AsRef<<HyperLogLog<T, W> as CounterLogic>::Backend> {
        let offset = index * self.logic.words_per_counter;
        let ptr = self.backend[offset].get();

        unsafe { std::slice::from_raw_parts(ptr, self.logic.words_per_counter) }
    }

    #[inline(always)]
    fn logic(&self) -> &HyperLogLog<T, W> {
        &self.logic
    }

    fn get_backend_mut(
        &mut self,
        index: usize,
    ) -> &mut <HyperLogLog<T, W> as CounterLogic>::Backend {
        let offset = index * self.logic.words_per_counter;
        let ptr = self.backend[offset].get();

        unsafe { std::slice::from_raw_parts_mut(ptr, self.logic.words_per_counter) }
    }

    fn get_counter(&self, index: usize) -> Self::Counter<'_> {
        let offset = index * self.logic.words_per_counter;
        let ptr = self.backend[offset].get();

        let bits = unsafe { std::slice::from_raw_parts_mut(ptr, self.logic.words_per_counter) };
        DefaultCounter {
            logic: self.logic.clone(), // TODO: avoid cloning the logic
            backend: bits,
        }
    }

    fn get_counter_mut(&mut self, index: usize) -> Self::CounterMut<'_> {
        let offset = index * self.logic.words_per_counter;
        let ptr = self.backend[offset].get();

        let bits = unsafe { std::slice::from_raw_parts_mut(ptr, self.logic.words_per_counter) };
        DefaultCounter {
            logic: self.logic.clone(),
            backend: bits,
        }
    }

    unsafe fn set_to(
        &self,
        index: usize,
        content: impl AsRef<<HyperLogLog<T, W> as CounterLogic>::Backend>,
    ) {
        let offset = index * self.logic.words_per_counter;
        for (c, &b) in self.backend[offset..].iter().zip(content.as_ref()) {
            *c.get() = b;
        }
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.backend.fill_with(|| UnsafeSyncCell::new(W::ZERO));
    }
}
