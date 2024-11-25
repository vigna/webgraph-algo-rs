use crate::utils::DefaultCounter;
use crate::{prelude::*, utils::MmapSlice};
use anyhow::{Context, Result};
use std::cell::{Cell, UnsafeCell};
use sux::traits::Word;
use webgraph::utils::SyncCell;

/// An array for counters implementing a shared [`CounterLogic`] whose backend
/// is a slice.
///
/// Note that we need a specific type for arrays slice backends as one
/// cannot create a slice of slices.
pub struct SliceCounterArray<L, W> {
    pub(super) logic: L,
    pub(super) backend: MmapSlice<SyncCell<W>>,
    pub(super) len: usize,
}

impl<L: CounterLogic, W> SliceCounterArray<L, W> {
    /// Returns the number of elements in the array, also referred to as its ‘length’.
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

impl<L: CounterLogic<Backend = [W]>, W> SliceCounterArray<L, W> {
    #[allow(dead_code)]
    pub(crate) fn as_slice(&self) -> &[W] {
        let len = self.backend.len();
        let ptr = UnsafeCell::raw_get(self.backend.as_slice() as *const [_] as *const _);
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }
}

impl<L: SliceCounterLogic<Backend = [W]>, W: Word> SliceCounterArray<L, W> {
    /// Creates a new counter slice with the provided logic allocating in-memory.
    ///
    /// # Arguments
    /// * `logic`: the counter logic to use.
    /// * `len`: the number of the counters in the array.
    pub fn new(logic: L, len: usize) -> Result<Self> {
        let num_backend_len = logic.backend_len();
        let bits = MmapSlice::from_closure(
            || SyncCell::new(W::ZERO),
            len * num_backend_len,
            TempMmapOptions::Default,
        )
        .with_context(|| "Could not create MmapSlice for slice backend")?;
        Ok(Self {
            logic,
            backend: bits,
            len,
        })
    }

    /// Creates a new counter slice with the provided logic allocating memory
    /// with the provided options.
    ///
    /// # Arguments
    /// * `logic`: the counter logic to use.
    /// * `len`: the number of the counters in the array.
    /// * `mmap_options`: the options to use in [MmapSlice].
    pub fn with_mmap(logic: L, len: usize, mmap_options: TempMmapOptions) -> Result<Self> {
        let num_backend_len = logic.backend_len();
        let bits = MmapSlice::from_closure(
            || SyncCell::new(W::ZERO),
            len * num_backend_len,
            mmap_options,
        )
        .with_context(|| "Could not create MmapSlice for slice backend")?;
        Ok(Self {
            logic,
            backend: bits,
            len,
        })
    }
}

impl<L: SliceCounterLogic<Backend = [W]> + Clone, W: Word> CounterArray<L>
    for SliceCounterArray<L, W>
{
    type Counter<'a> = DefaultCounter<L, &'a L, &'a [W]> where Self: 'a;

    fn get_backend(&self, index: usize) -> &L::Backend {
        let offset = index * self.logic.backend_len();
        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        unsafe {
            &*(self.backend[offset..][..self.logic.backend_len()].as_ref() as *const [SyncCell<W>]
                as *const [Cell<W>] as *const [W])
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

impl<L: SliceCounterLogic<Backend = [W]> + Clone, W: Word> CounterArrayMut<L>
    for SliceCounterArray<L, W>
{
    type CounterMut<'a> = DefaultCounter<L, &'a L, &'a mut [W]> where Self: 'a;

    fn get_backend_mut(&mut self, index: usize) -> &mut L::Backend {
        let offset = index * self.logic.backend_len();

        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        unsafe {
            &mut *(self.backend[offset..][..self.logic.backend_len()].as_mut()
                as *mut [SyncCell<W>] as *mut [Cell<W>] as *mut [W])
        }
    }

    fn get_counter_mut(&mut self, index: usize) -> Self::CounterMut<'_> {
        let logic = &self.logic;

        // We have to extract manually the backend because get_backend_mut
        // borrows self mutably, but we need to borrow just self.backend.
        let offset = index * self.logic.backend_len();

        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        let backend = unsafe {
            &mut *(self.backend[offset..][..self.logic.backend_len()].as_mut()
                as *mut [SyncCell<W>] as *mut [Cell<W>] as *mut [W])
        };

        DefaultCounter::new(logic, backend)
    }

    unsafe fn set(&self, index: usize, content: &L::Backend) {
        debug_assert!(content.as_ref().len() == self.logic.backend_len());
        let offset = index * self.logic.backend_len();
        for (c, &b) in self.backend[offset..].iter().zip(content.as_ref()) {
            c.set(b)
        }
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.backend
            .iter_mut()
            .for_each(|v| unsafe { v.set(W::ZERO) });
    }
}
