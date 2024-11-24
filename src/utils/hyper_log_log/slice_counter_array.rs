use super::*;
use crate::utils::DefaultCounter;
use crate::{prelude::*, utils::MmapSlice};
use common_traits::{CastableFrom, UpcastableInto};
use std::cell::{Cell, UnsafeCell};
use std::hash::*;
use sux::traits::Word;

#[repr(transparent)]
pub struct SyncCell<T: ?Sized>(Cell<T>);

impl<T> SyncCell<T> {
    #[inline(always)]
    fn new(value: T) -> Self {
        Self(Cell::new(value))
    }
}

impl<T> SyncCell<[T]> {
    #[inline(always)]
    pub fn as_slice_of_cells(&self) -> &[SyncCell<T>] {
        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        let slice_of_cells =
            unsafe { &*(self as *const SyncCell<[T]> as *const Cell<[T]>) }.as_slice_of_cells();
        unsafe { &*(slice_of_cells as *const [Cell<T>] as *const [SyncCell<T>]) }
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

pub struct SliceCounterArray<L, W> {
    pub(super) logic: L,
    pub(super) backend: MmapSlice<SyncCell<W>>,
    pub(super) len: usize,
}

impl<L: CounterLogic<Backend = [W]>, W> SliceCounterArray<L, W> {
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

impl<
        L: SliceCounterLogic<Backend = [W]> + Clone,
        W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>,
    > CounterArray<L> for SliceCounterArray<L, W>
{
    type Counter<'a> = DefaultCounter<L, &'a L, &'a [W]> where Self: 'a;

    fn get_backend(&self, index: usize) -> &L::Backend {
        let offset = index * self.logic.words_per_counter();
        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        unsafe {
            &*(self.backend[offset..][..self.logic.words_per_counter()].as_ref()
                as *const [SyncCell<W>] as *const [Cell<W>] as *const [W])
        }
    }

    #[inline(always)]
    fn logic(&self) -> &L {
        &self.logic
    }

    fn get_counter(&self, index: usize) -> Self::Counter<'_> {
        DefaultCounter::new(&self.logic, self.get_backend(index))
    }
}

impl<
        L: SliceCounterLogic<Backend = [W]> + Clone,
        W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>,
    > CounterArrayMut<L> for SliceCounterArray<L, W>
{
    type CounterMut<'a> = DefaultCounter<L, &'a L, &'a mut [W]> where Self: 'a;

    fn get_backend_mut(&mut self, index: usize) -> &mut L::Backend {
        let offset = index * self.logic.words_per_counter();

        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        unsafe {
            &mut *(self.backend[offset..][..self.logic.words_per_counter()].as_mut()
                as *mut [SyncCell<W>] as *mut [Cell<W>] as *mut [W])
        }
    }

    fn get_counter_mut(&mut self, index: usize) -> Self::CounterMut<'_> {
        let logic = &self.logic;

        // We have to extract manually the backend because get_backend_mut
        // borrows self mutably, but we need to borrow just self.backend.
        let offset = index * self.logic.words_per_counter();

        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        let backend = unsafe {
            &mut *(self.backend[offset..][..self.logic.words_per_counter()].as_mut()
                as *mut [SyncCell<W>] as *mut [Cell<W>] as *mut [W])
        };

        DefaultCounter::new(logic, backend)
    }

    unsafe fn set(&self, index: usize, content: &L::Backend) {
        debug_assert!(content.as_ref().len() == self.logic.words_per_counter());
        let offset = index * self.logic.words_per_counter();
        for (c, &b) in self.backend[offset..].iter().zip(content.as_ref()) {
            c.set(b)
        }
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.backend.fill_with(|| SyncCell::new(W::ZERO));
    }
}
