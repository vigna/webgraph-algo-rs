use std::cell::UnsafeCell;

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
    /// Calling this method while another reference to the same cell is [undefined behavior].
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
