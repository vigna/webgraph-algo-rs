use std::cell::UnsafeCell;
use sux::traits::Word;

/// Trait that allows mutable access to a value in a mutable slice from an immutable reference.
///
/// This does not perform bounds-checking nor does it ensure exclusive access to the data nor
/// does it ensure produced references are not dangling once the original slice goes out of scope.
///
/// This can lead to [undefined behavior] if used on immutable data.
///
/// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
pub trait UnsafeSliceWrite<T> {
    /// Writes `value` in position `index` without a mutable reference.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds `index` is [undefined behavior].
    ///
    /// Calling this method in a concurrent context with the same index more than once
    /// at the same time is [undefined behavior].
    /// Mutual exclusion is to be guaranteed by the caller.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline(always)]
    unsafe fn write_once(&self, index: usize, value: T) {
        *self.get_mut_unsafe(index) = value;
    }

    /// Gets a mutable slice from an immutable one.
    ///
    /// # Safety
    ///
    /// Using the returned reference in a concurrent context to access the same index is [undefined behavior].
    /// Mutual exclusion is to be guaranteed by the caller.
    ///
    /// The returned reference may be dangling if the original slice goes out of scope.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::mut_from_ref)]
    unsafe fn as_mut_slice_unsafe(&self) -> &mut [T];

    /// Gets a mutable pointer to the value in position `index`.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds `index` is [undefined behavior].
    ///
    /// Dereferencig the pointer returned by this method in a concurrent context with the same
    /// index more than once is [undefined behavior].
    /// Mutual exclusion is to be guaranteed by the caller.
    ///
    /// The returned pointer may be dangling if the original slice goes out of scope.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn get_mut_unsafe(&self, index: usize) -> *mut T;
}

/// Wrapper on [`UnsafeCell`] that allows easy reads and writes and implements [`Sync`].
#[repr(transparent)]
pub struct UnsafeSyncCell<T: ?Sized> {
    cell: UnsafeCell<T>,
}

impl<T> UnsafeSyncCell<T> {
    pub fn new(v: T) -> Self {
        Self {
            cell: UnsafeCell::new(v),
        }
    }
}

unsafe impl<T> Sync for UnsafeSyncCell<T> {}

impl<T: Copy> UnsafeSyncCell<T> {
    /// Reads the wrapped value.
    #[inline(always)]
    pub fn read(&self) -> T {
        unsafe { *self.cell.get() }
    }
}

impl<T> UnsafeSyncCell<T> {
    /// The size of the wrapped type
    const TYPE_SIZE: usize = std::mem::size_of::<T>();

    /// The size of the wrapper
    const CELL_SIZE: usize = std::mem::size_of::<Self>();

    /// Writes to the wrapped [`UnsafeCell`] without a mutable refernce.
    ///
    /// # Safety
    ///
    /// Calling this method while a mutable reference obtained with [`Self::as_mut_unsafe`]
    /// still exists is [udefined behavior].
    ///
    /// Calling this method while another thread is reading the value is [undefined behavior].
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline(always)]
    pub unsafe fn write_unsafe(&self, value: T) {
        *self.cell.get() = value;
    }

    /// Returns a mutable reference to the value wrapped by [`UnsafeCell`].
    ///
    /// # Safety
    ///
    /// Calling this method while another reference to the same cell exists is [undefined behavior].
    ///
    /// Calling [`Self::read`] while a reference returned by this method still exists is
    /// [undefined behavior].
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    pub unsafe fn as_mut_unsafe(&self) -> &mut T {
        &mut *self.cell.get()
    }
}

impl<T> UnsafeSyncCell<[T]> {
    /// Returns a `&[UnsafeSyncCell<T>]` from a `&UnsafeSyncCell<[T]>`.
    #[inline(always)]
    pub fn as_slice_of_cells(&self) -> &[UnsafeSyncCell<T>] {
        debug_assert_eq!(
            UnsafeSyncCell::<T>::TYPE_SIZE,
            UnsafeSyncCell::<T>::CELL_SIZE
        );
        unsafe { &*(self as *const Self as *const [UnsafeSyncCell<T>]) }
    }
}

impl<T> UnsafeSliceWrite<T> for UnsafeSyncCell<[T]> {
    #[inline(always)]
    unsafe fn as_mut_slice_unsafe(&self) -> &mut [T] {
        debug_assert_eq!(
            UnsafeSyncCell::<T>::TYPE_SIZE,
            UnsafeSyncCell::<T>::CELL_SIZE
        );
        unsafe {
            std::slice::from_raw_parts_mut(
                (*self.cell.get()).as_ptr() as *mut T,
                (*self.cell.get()).len(),
            )
        }
    }

    #[inline(always)]
    unsafe fn get_mut_unsafe(&self, index: usize) -> *mut T {
        debug_assert_eq!(
            UnsafeSyncCell::<T>::TYPE_SIZE,
            UnsafeSyncCell::<T>::CELL_SIZE
        );
        debug_assert!(index < unsafe { (*self.cell.get()).len() });
        unsafe { ((*self.cell.get()).as_ptr() as *mut T).add(index) }
    }
}

impl<T> UnsafeSliceWrite<T> for [UnsafeSyncCell<T>] {
    #[inline(always)]
    unsafe fn as_mut_slice_unsafe(&self) -> &mut [T] {
        debug_assert_eq!(
            UnsafeSyncCell::<T>::TYPE_SIZE,
            UnsafeSyncCell::<T>::CELL_SIZE
        );
        std::slice::from_raw_parts_mut(self.as_ptr() as *mut T, self.len())
    }

    #[inline(always)]
    unsafe fn get_mut_unsafe(&self, index: usize) -> *mut T {
        debug_assert!(index < self.len());
        unsafe { self.get_unchecked(index).cell.get() }
    }
}

/// Conversion trait that allows to wrap any type `T` into an [`UnsafeSyncCell`].
pub trait InteriorMutability {
    /// Wraps a mutable reference into an [`UnsafeSyncCell`] and returns a mutable
    /// reference to it.
    fn as_interior_mut(&mut self) -> &mut UnsafeSyncCell<Self>;
}

impl<T> InteriorMutability for T {
    #[inline(always)]
    fn as_interior_mut(&mut self) -> &mut UnsafeSyncCell<Self> {
        debug_assert_eq!(
            UnsafeSyncCell::<T>::TYPE_SIZE,
            UnsafeSyncCell::<T>::CELL_SIZE
        );
        unsafe { &mut *(self as *mut Self as *mut UnsafeSyncCell<Self>) }
    }
}

/// Coversion trait that allows to wrap any slice of `T` into an [`UnsafeSyncCell`].
pub trait SliceInteriorMutability<T> {
    /// Wraps a mutable slice `&mut [T]` into an [`UnsafeSyncCell`] and returns a mutable reference
    /// `&mut UnsafeSyncCell<[T]>`.
    fn as_interior_mut_slice(&mut self) -> &mut UnsafeSyncCell<[T]>;

    /// Wraps a mutable slice `&mut [T]` into a slice of `UnsafeSyncCell<T>`.
    #[inline(always)]
    fn as_mut_slice_of_cells(&mut self) -> &[UnsafeSyncCell<T>] {
        self.as_interior_mut_slice().as_slice_of_cells()
    }
}

impl<T> SliceInteriorMutability<T> for [T] {
    #[inline(always)]
    fn as_interior_mut_slice(&mut self) -> &mut UnsafeSyncCell<[T]> {
        debug_assert_eq!(
            UnsafeSyncCell::<T>::TYPE_SIZE,
            UnsafeSyncCell::<T>::CELL_SIZE
        );
        unsafe { &mut *(self as *mut [T] as *mut UnsafeSyncCell<[T]>) }
    }
}

/// A dictionary that can only count the number of distinct elements that have
/// been added so far.
///
/// Typical implementations will be approximated (e.g.,
/// [`HyperLogLogCounter`][`super::hyper_log_log::HyperLogLogCounter`]).
pub trait Counter<T> {
    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&mut self, element: T);

    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self) -> f64;

    /// Clears the counter.
    fn clear(&mut self);

    /// Sets the contents of `self` to the contents of `other`.
    fn set_to(&mut self, other: &Self);
}

/// A [`Counter`] that can be merged with other counters.
pub trait MergeableCounter<T>: Counter<T> {
    /// Merges `other` onto `self` inplace.
    ///
    /// After this call, the state of the counter is the same as if also the
    /// elements added to `other` had been added (i.e., the dictionary
    /// represents the union of the two dictionaries)
    ///
    /// `other` is not modified but `self` is.
    ///
    /// # Arguments
    ///
    /// * `other`: the counter to merge onto `self`.
    fn merge(&mut self, other: &Self);
}

/// A counter capable of using external allocations during its lifetime in order to
/// avoid to allocate all its data structures each time.
///
/// You can obtain a `ThreadHelper` by calling [`HyperLogLogArray::get_thread_helper`].
pub trait ThreadHelperCounter<'a, H> {
    /// Sets the counter to use the specified thread helper.
    fn use_thread_helper(&mut self, helper: &'a mut H);

    /// Stops the counter from using the thread helper.
    fn remove_thread_helper(&mut self);
}

/// An HyperLogLogCounter.
///
/// This represents a counter capable of performing the `HyperLogLog` algorithm.
pub trait HyperLogLog<'a, T, W: Word, H>:
    MergeableCounter<T> + ThreadHelperCounter<'a, H> + PartialEq + Eq
{
}
impl<'a, T, W: Word, H, I: MergeableCounter<T> + ThreadHelperCounter<'a, H> + PartialEq + Eq>
    HyperLogLog<'a, T, W, H> for I
{
}

/// An array of counter implementing [`HyperLogLog`].
pub trait HyperLogLogArray<T, W: Word> {
    /// The type of counter this array contains.
    ///
    /// Note how lifetime `'h` is the lifetime of the `ThreadHelper` reference
    /// while `'d` is the lifetime of the data pointed to by the borrowed counter.
    type Counter<'d, 'h>: HyperLogLog<'h, T, W, Self::ThreadHelper>
    where
        Self: 'd,
        Self: 'h;

    /// The type of the owned counter with all the relevant data copied into itself.
    ///
    /// Obtained when calling [`CachableCounter::get_copy`], [`CachableCounter::into_owned`]
    /// or [`CachableCounter::copy_into_owned`].
    type OwnedCounter<'h>: MergeableCounter<T>
        + ThreadHelperCounter<'h, Self::ThreadHelper>
        + PartialEq
        + Eq
    where
        Self: 'h;

    /// The type of the thread helper struct with all the data structures
    /// already allocated.
    ///
    /// Used by [`ThreadHelperCounter::use_thread_helper`].
    type ThreadHelper;

    /// Returns a new [`Self::ThreadHelper`] by
    /// performing the necessary allocations.
    fn get_thread_helper(&self) -> Self::ThreadHelper;

    /// Returns the number of counters in the array.
    fn len(&self) -> usize;

    /// Returns the borrowed counter at the specified index using an immutable reference
    /// to the underlying array.
    ///
    /// # Arguments
    /// * `index`: the index of the counter to get.
    ///
    /// # Safety
    ///
    /// It is up to the caller to avoid data races when using this function.
    /// In particular reading from or writing to a borrowed counter that is already being written to
    /// is [undefined behavior], while reading from a counter that is only being read from is perfectly sound.
    ///
    /// Reading from or writing to an owned counter is always sound, as the data contained within is owned
    /// by the counter and not shared with the underlying array.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn get_counter_from_shared<'h>(&self, index: usize) -> Self::Counter<'_, 'h>;

    /// Returns the borrowed counter at the specified index.
    ///
    /// # Arguments
    /// * `index`: the index of the counter to get.
    #[inline(always)]
    fn get_counter<'h>(&mut self, index: usize) -> Self::Counter<'_, 'h> {
        unsafe {
            // Safety: We have a mutable reference so no other references exist
            self.get_counter_from_shared(index)
        }
    }

    /// Returns the owned counter at the specified index.
    ///
    /// # Arguments
    /// * `index`: the index of the counter to get.
    fn get_owned_counter<'h>(&self, index: usize) -> Self::OwnedCounter<'h>;

    /// Returns `true` if the vector contains no counters.
    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Resets all counters
    #[inline(always)]
    fn clear(&mut self) {
        for i in 0..self.len() {
            self.get_counter(i).clear();
        }
    }

    /// Swaps the contents of `self` with the contents of `other`.
    ///
    /// # Arguments
    /// * `other`: the array to swap contents with.
    #[inline(always)]
    fn swap_with(&mut self, other: &mut Self)
    where
        Self: Sized,
    {
        std::mem::swap(self, other);
    }
}
