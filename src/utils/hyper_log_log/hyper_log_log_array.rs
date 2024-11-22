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

pub struct HyperLogLogArray<T, W: Word, H: BuildHasher = BuildHasherDefault<DefaultHasher>> {
    pub(super) logic: HyperLogLog<T, W, H>,
    pub(super) backend: MmapSlice<UnsafeSyncCell<W>>,
    pub(super) len: usize,
}

impl<T, W: Word, H: BuildHasher> HyperLogLogArray<T, W, H> {
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
}

impl<
        T: Hash,
        W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>,
        H: BuildHasher + Clone,
    > CounterArray<T, HyperLogLog<T, W, H>> for HyperLogLogArray<T, W, H>
{
    type Counter<'a> = DefaultCounter<T, W, H, HyperLogLog<T, W, H>, &'a HyperLogLog<T, W, H>, &'a mut [W]> where T: 'a, W: 'a, H: 'a;

    fn get_backend(&self, index: usize) -> &<HyperLogLog<T, W, H> as CounterLogic<T>>::Backend {
        let offset = index * self.logic.words_per_counter();
        let ptr = self.backend[offset].get();

        unsafe { std::slice::from_raw_parts(ptr, self.logic.words_per_counter()) }
    }

    #[inline(always)]
    fn get_counter_logic(&self) -> &HyperLogLog<T, W, H> {
        &self.logic
    }

    fn get_backend_mut(
        &mut self,
        index: usize,
    ) -> &mut <HyperLogLog<T, W, H> as CounterLogic<T>>::Backend {
        let offset = index * self.logic.words_per_counter();
        let ptr = self.backend[offset].get();

        unsafe { std::slice::from_raw_parts_mut(ptr, self.logic.words_per_counter()) }
    }

    fn get_mut_counter(&mut self, index: usize) -> Self::Counter<'_> {
        let offset = index * self.logic.words_per_counter();
        let ptr = self.backend[offset].get();

        let bits = unsafe { std::slice::from_raw_parts_mut(ptr, self.logic.words_per_counter()) }
        Self::Counter {
            backend: bits,
            logic: &self.logic,
            _marker: std::marker::PhantomData,
        }
    }

    unsafe fn set_to(&self, index: usize, content: impl AsRef<[W]>) {
        let offset = index * self.logic.words_per_counter();
        for (c, &b) in self.backend[offset..].iter().zip(content.as_ref()) {
            *c.get() = b;
        }
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.backend.fill_with(|| UnsafeSyncCell::new(W::ZERO));
    }
}
