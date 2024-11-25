use std::borrow::Borrow;

/// A logic to interact with counters.
pub trait CounterLogic {
    /// The type of items this counter accepts.
    type Item;
    /// The type of the counter's backend
    type Backend: ?Sized;
    /// The counter's concrete type
    type Counter<'a>: CounterMut<Self>
    where
        Self: 'a;

    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&self, counter: &mut Self::Backend, element: impl Borrow<Self::Item>);

    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self, counter: &Self::Backend) -> f64;

    /// Clears the counter.
    fn clear(&self, counter: &mut Self::Backend);

    /// Sets the contents of `self` to the contents of `other`.
    fn set(&self, dst: &mut Self::Backend, src: &Self::Backend);

    /// Creates a new empty counter with this logic.
    fn new_counter(&self) -> Self::Counter<'_>;
}

/// A logic to interact with counters capable of merging contents.
pub trait MergeCounterLogic: CounterLogic {
    /// The type of the helper use in merge calculations.
    type Helper;

    /// Creates a new helper to use in merge operations.
    fn new_helper(&self) -> Self::Helper;

    /// Merges `src` into `dst`.
    fn merge(&self, dst: &mut Self::Backend, src: &Self::Backend) {
        let mut helper = self.new_helper();
        self.merge_with_helper(dst, src, &mut helper);
    }

    /// Merges `src` into `dst` using the provided helper to avoid
    /// useless allocations.
    fn merge_with_helper(
        &self,
        dst: &mut Self::Backend,
        src: &Self::Backend,
        helper: &mut Self::Helper,
    );
}

/// Trait implemented by counters whose backend is a slice of `W`.
pub trait SliceCounterLogic: CounterLogic {
    /// The number of `W` each counter uses.
    fn words_per_counter(&self) -> usize;
}

/// An immutable counter instance
pub trait Counter<L: CounterLogic + ?Sized> {
    /// The owned type of this counter
    type OwnedCounter: CounterMut<L>;

    /// Returns the counter's logic.
    fn get_logic(&self) -> &L;

    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self) -> f64;

    /// Returns a reference to the counter's backend.
    fn as_backend(&self) -> &L::Backend;

    /// Converts this counter into its owned version capable of mutating.
    fn into_owned(self) -> Self::OwnedCounter;
}

/// A mutable counter instance.
pub trait CounterMut<L: CounterLogic + ?Sized>: Counter<L> {
    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&mut self, element: impl Borrow<L::Item>);

    /// Clears the counter.
    fn clear(&mut self);

    /// Returns a mutable reference to the counter's backend.
    fn as_backend_mut(&mut self) -> &mut L::Backend;

    /// Sets the contents of `self` to the contents of `other`.
    fn set(&mut self, other: &L::Backend);
}

/// A counter capable of merging its contents with other counters.
pub trait MergeCounter<L: MergeCounterLogic + ?Sized>: CounterMut<L> {
    /// Merges `other` into `self`.
    fn merge(&mut self, other: &L::Backend) {
        let mut helper = self.get_logic().new_helper();
        self.merge_with_helper(other, &mut helper);
    }

    /// Merges `other` into `self` using the provided helper to avoid
    /// useless allocations.
    fn merge_with_helper(&mut self, other: &L::Backend, helper: &mut L::Helper);
}

/// An array of immutable counters implementing a [CounterLogic].
pub trait CounterArray<L: CounterLogic> {
    /// The type of immutable counter contained in the array.
    type Counter<'a>: Counter<L>
    where
        Self: 'a;

    /// Returns the logic used by the counters in the array.
    fn logic(&self) -> &L;

    /// Returns the counter at the specified index as an immutable counter.
    fn get_counter(&self, index: usize) -> Self::Counter<'_>;

    /// Returns an immutable reference to the backend of the counter at the specified index.
    fn get_backend(&self, index: usize) -> &L::Backend;
}

/// An array of mutable counters implementing a [CounterLogic].
pub trait CounterArrayMut<L: CounterLogic>: CounterArray<L> {
    /// The type of mutable counter contained in the array.
    type CounterMut<'a>: CounterMut<L>
    where
        Self: 'a;

    /// Returns the counter at the specified index as a mutable counter.
    fn get_counter_mut(&mut self, index: usize) -> Self::CounterMut<'_>;

    /// Returns a mutable reference to the backend of the counter at the specified index.
    fn get_backend_mut(&mut self, index: usize) -> &mut L::Backend;

    /// Sets the contents of the counter at `index` to `content`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `content` has the same length as the counter
    /// at `index`. The caller must ensure that there are no data races.
    unsafe fn set(&self, index: usize, content: &L::Backend);

    /// Resets all counters in the array.
    fn clear(&mut self);
}
