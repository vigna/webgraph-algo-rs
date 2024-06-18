/// Trait that allows mutable access to a value in a mutable slice from an immutable reference.
///
/// This does not perform bounds-checking nor does it ensure exclusive access to the data nor
/// does it ensure produced references are not dangling once the original slice goes out of scope.
///
/// This can lead to [undefined behavior] if used on immutable data
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
    unsafe fn as_mut_slice_unsafe(&self) -> &mut [T];

    /// Gets a mutable pointer to the value in position `index`.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds `index` is [undefined behavior].
    ///
    /// Calling this method and using the returned reference in a concurrent context with the same
    /// index more than once is [undefined behavior].
    /// Mutual exclusion is to be guaranteed by the caller.
    ///
    /// The returned pointer may be dangling if the original slice goes out of scope.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::mut_from_ref)]
    unsafe fn get_mut_unsafe(&self, index: usize) -> *mut T;
}

impl<T> UnsafeSliceWrite<T> for [T] {
    #[inline(always)]
    unsafe fn write_once(&self, index: usize, value: T) {
        *(self.as_ptr() as *mut T).add(index) = value;
    }

    #[inline(always)]
    unsafe fn as_mut_slice_unsafe(&self) -> &mut [T] {
        std::slice::from_raw_parts_mut(self.as_ptr() as *mut T, self.len())
    }

    #[inline(always)]
    unsafe fn get_mut_unsafe(&self, index: usize) -> *mut T {
        (self.as_ptr() as *mut T).add(index)
    }
}

/// Trait that allows mutable access to a value from an immutable reference
///
/// This does not ensure exclusive access to the data nor does it ensure produced
/// references are not dangling once the original reference goes out of scope.
pub trait UnsafeWrite {
    /// Writes `value` without a mutable reference.
    ///
    /// # Safety
    ///
    /// Calling this method in a concurrent context more than once
    /// at the same time is [undefined behavior].
    /// Mutual exclusion is to be guaranteed by the caller.
    ///
    /// This could conflict with Rust compiler's optimizations on `readonly` memory and lead
    /// to [undefined behavior].
    /// As such you should always mark memory that will be mutated with this as `mut`.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    unsafe fn write_unsafe(&self, value: Self);

    /// Gets a mutable reference from an immutable one.
    ///
    /// # Safety
    ///
    /// Mutual exclusion is to be guaranteed by the caller.
    ///
    /// The returned reference may be dangling if the original reference goes out of scope.
    ///
    /// This could conflict with Rust compiler's optimizations on `readonly` memory and lead
    /// to [undefined behavior].
    /// As such you should always mark memory that will be mutated with this as `mut`.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[allow(clippy::mut_from_ref)]
    unsafe fn as_mut_unsafe(&self) -> &mut Self;
}

impl<T> UnsafeWrite for T {
    #[allow(invalid_reference_casting)]
    #[inline(always)]
    unsafe fn write_unsafe(&self, value: Self) {
        *(self as *const Self as *mut Self) = value;
    }

    #[allow(invalid_reference_casting)]
    #[inline(always)]
    unsafe fn as_mut_unsafe(&self) -> &mut Self {
        &mut *(self as *const Self as *mut Self)
    }
}
