use crate::utils::DefaultCounter;
use crate::{prelude::*, utils::MmapSlice};
use anyhow::{Context, Result};
use sux::traits::Word;
use sync_cell_slice::SyncCell;

/// An array for counters implementing a shared [`CounterLogic`] whose backend
/// is a slice.
///
/// Note that we need a specific type for arrays slice backends as one
/// cannot create a slice of slices.
pub struct SliceCounterArray<L, W, S> {
    pub(super) logic: L,
    pub(super) backend: S,
    pub(super) len: usize,
    _marker: std::marker::PhantomData<W>,
}

impl<L: SliceCounterLogic, W, S> SliceCounterArray<L, W, S> {
    /// Returns the number of counters in the array.
    #[inline(always)]
    pub fn len(&self) -> usize {
        debug_assert!(self.len % self.logic.backend_len() == 0);
        self.len / self.logic.backend_len()
    }

    /// Returns `true` if the array contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<L: CounterLogic<Backend = [W]>, W, S: AsRef<[SyncCell<W>]>> AsRef<[W]>
    for SliceCounterArray<L, W, S>
{
    #[allow(dead_code)]
    fn as_ref(&self) -> &[W] {
        // SAFETY: SyncCell<W> has the same memory layout as W
        unsafe { &*(self.backend.as_ref() as *const [SyncCell<W>] as *const [W]) }
    }
}

impl<L: SliceCounterLogic<Backend = [W]>, W: Word> SliceCounterArray<L, W, MmapSlice<SyncCell<W>>> {
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
            _marker: std::marker::PhantomData,
        })
    }

    /// Creates a new counter slice with the provided logic allocating memory
    /// by memory mapping, using the provided options.
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
            _marker: std::marker::PhantomData,
        })
    }
}

impl<L: SliceCounterLogic<Backend = [W]> + Clone, W: Word, S: AsRef<[SyncCell<W>]>> CounterArray<L>
    for SliceCounterArray<L, W, S>
{
    type Counter<'a>
        = DefaultCounter<L, &'a L, &'a [W]>
    where
        Self: 'a;

    #[inline(always)]
    fn get_backend(&self, index: usize) -> &L::Backend {
        let offset = index * self.logic.backend_len();
        // SAFETY: `SyncCell<W>` has the same memory layout as `W`.
        unsafe {
            &*(&self.backend.as_ref()[offset..][..self.logic.backend_len()]
                as *const [SyncCell<W>] as *const [W])
        }
    }

    #[inline(always)]
    fn logic(&self) -> &L {
        &self.logic
    }

    #[inline(always)]
    fn get_counter(&self, index: usize) -> Self::Counter<'_> {
        DefaultCounter::new(&self.logic, self.get_backend(index))
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.len
    }
}

impl<
        L: SliceCounterLogic<Backend = [W]> + Clone,
        W: Word,
        S: AsRef<[SyncCell<W>]> + AsMut<[SyncCell<W>]>,
    > CounterArrayMut<L> for SliceCounterArray<L, W, S>
{
    type CounterMut<'a>
        = DefaultCounter<L, &'a L, &'a mut [W]>
    where
        Self: 'a;

    #[inline(always)]
    fn get_backend_mut(&mut self, index: usize) -> &mut L::Backend {
        let offset = index * self.logic.backend_len();
        // SAFETY: `SyncCell<W>` has the same memory layout as `W`.
        unsafe {
            &mut *(&mut self.backend.as_mut()[offset..][..self.logic.backend_len()]
                as *mut [SyncCell<W>] as *mut [W])
        }
    }

    #[inline(always)]
    fn get_counter_mut(&mut self, index: usize) -> Self::CounterMut<'_> {
        let logic = &self.logic;

        // We have to extract manually the backend because get_backend_mut
        // borrows self mutably, but we need to borrow just self.backend.
        let offset = index * self.logic.backend_len();

        // SAFETY: `SyncCell<T>` has the same memory layout os `Cell<T>`, which
        // has the same memory layout as `T`.
        let backend = unsafe {
            &mut *(&mut self.backend.as_mut()[offset..][..self.logic.backend_len()]
                as *mut [SyncCell<W>] as *mut [W])
        };

        DefaultCounter::new(logic, backend)
    }

    #[inline(always)]
    unsafe fn set(&self, index: usize, content: &L::Backend) {
        debug_assert!(content.as_ref().len() == self.logic.backend_len());
        let offset = index * self.logic.backend_len();
        for (c, &b) in self.backend.as_ref()[offset..].iter().zip(content.as_ref()) {
            c.set(b)
        }
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.backend
            .as_mut()
            .iter_mut()
            .for_each(|v| unsafe { v.set(W::ZERO) });
    }
}
