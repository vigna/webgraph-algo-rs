/// Trait that allows mutable access to a value in a slice from an immutable reference.
///
/// This does not perform bounds-checking nor does it ensure exclusive access to the data nor
/// does it ensure produced references are not dangling once the original slice goes out of scope.
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
    unsafe fn write_once(&self, index: usize, value: T);

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
    unsafe fn as_mut_unsafe(&self) -> &mut [T];

    /// Gets a mutable reference to the value in position `index`.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds `index` is [undefined behavior].
    ///
    /// Calling this method and using the returned reference in a concurrent context with the same
    /// index more than once is [undefined behavior].
    /// Mutual exclusion is to be guaranteed by the caller.
    ///
    /// The returned reference may be dangling if the original slice goes out of scope.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::mut_from_ref)]
    unsafe fn get_mut_unsafe(&self, index: usize) -> &mut T;
}

impl<T> UnsafeSliceWrite<T> for [T] {
    #[inline(always)]
    unsafe fn write_once(&self, index: usize, value: T) {
        *(self.as_ptr() as *mut T).add(index) = value;
    }

    #[inline(always)]
    unsafe fn as_mut_unsafe(&self) -> &mut [T] {
        std::slice::from_raw_parts_mut(self.as_ptr() as *mut T, self.len())
    }

    #[inline(always)]
    unsafe fn get_mut_unsafe(&self, index: usize) -> &mut T {
        &mut *(self.as_ptr() as *mut T).add(index)
    }
}
