use super::*;
use crate::utils::DefaultCounter;
use crate::{prelude::*, utils::MmapSlice};
use common_traits::{CastableFrom, UpcastableInto};
use std::cell::{Cell, UnsafeCell};
use std::hash::*;
use sux::traits::Word;

#[repr(transparent)]
pub(super) struct SyncCell<T>(Cell<T>);

impl<T> SyncCell<T> {
    #[inline(always)]
    fn new(value: T) -> Self {
        Self(Cell::new(value))
    }

    fn set(&self, value: T) {
        self.0.set(value)
    }
}

impl<T: Default> Default for SyncCell<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new(T::default())
    }
}

unsafe impl<T: Sync> Sync for SyncCell<T> {}

impl<T> std::ops::Deref for SyncCell<T> {
    type Target = Cell<T>;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub struct HyperLogLogArray<T, W: Word> {
    pub(super) logic: HyperLogLog<T, W>,
    pub(super) backend: MmapSlice<SyncCell<W>>,
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
    type Counter<'a> = DefaultCounter<HyperLogLog<T, W>, &'a HyperLogLog<T, W>, &'a [W]> where Self: 'a;

    fn get_backend(&self, index: usize) -> &<HyperLogLog<T, W> as CounterLogic>::Backend {
        let offset = index * self.logic.words_per_counter;
        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        unsafe {
            &*(self.backend[offset..][..self.logic.words_per_counter].as_ref()
                as *const [SyncCell<W>] as *const [Cell<W>] as *const [W])
        }
    }

    #[inline(always)]
    fn logic(&self) -> &HyperLogLog<T, W> {
        &self.logic
    }

    fn get_counter(&self, index: usize) -> Self::Counter<'_> {
        DefaultCounter::new(&self.logic, self.get_backend(index))
    }
}

impl<T: Hash, W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>>
    CounterArrayMut<HyperLogLog<T, W>> for HyperLogLogArray<T, W>
{
    type CounterMut<'a> = DefaultCounter<HyperLogLog<T, W>, &'a HyperLogLog<T, W>, &'a mut [W]> where Self: 'a;

    fn get_backend_mut(
        &mut self,
        index: usize,
    ) -> &mut <HyperLogLog<T, W> as CounterLogic>::Backend {
        let offset = index * self.logic.words_per_counter;

        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        unsafe {
            &mut *(self.backend[offset..][..self.logic.words_per_counter].as_mut()
                as *mut [SyncCell<W>] as *mut [Cell<W>] as *mut [W])
        }
    }

    fn get_counter_mut(&mut self, index: usize) -> Self::CounterMut<'_> {
        let logic = &self.logic;

        // We have to extract manually the backend because get_backend_mut
        // borrows self mutably, but we need to borrow just self.backend.
        let offset = index * self.logic.words_per_counter;

        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        let backend = unsafe {
            &mut *(self.backend[offset..][..self.logic.words_per_counter].as_mut()
                as *mut [SyncCell<W>] as *mut [Cell<W>] as *mut [W])
        };

        DefaultCounter::new(logic, backend)
    }

    unsafe fn set(&self, index: usize, content: &<HyperLogLog<T, W> as CounterLogic>::Backend) {
        debug_assert!(content.as_ref().len() == self.logic.words_per_counter);
        let offset = index * self.logic.words_per_counter;
        for (c, &b) in self.backend[offset..].iter().zip(content.as_ref()) {
            c.set(b)
        }
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.backend.fill_with(|| SyncCell::new(W::ZERO));
    }
}
