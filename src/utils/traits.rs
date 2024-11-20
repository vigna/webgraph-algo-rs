use sux::traits::Word;

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
/// You can obtain a `ThreadHelper` by calling [`CounterArray::get_thread_helper`].
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

/// An array of counters.
pub trait CounterArray<T, W: Word> {
    /// The type of counter this array contains.
    ///
    /// Note how lifetime `'h` is the lifetime of the `ThreadHelper` reference
    /// while `'d` is the lifetime of the data pointed to by the borrowed counter.
    type Counter<'d, 'h>: MergeableCounter<T>
        + ThreadHelperCounter<'h, Self::ThreadHelper>
        + PartialEq
        + Eq
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

    fn get_slice(&self, index: usize) -> &[W];

    unsafe fn get_mut_slice(&self, index: usize) -> &mut [W];
}
