pub trait CounterLogic<T> {
    type Backend: ?Sized;

    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&self, counter: impl AsMut<Self::Backend>, element: T);

    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self, counter: impl AsRef<Self::Backend>) -> f64;

    /// Clears the counter.
    fn clear(&self, counter: impl AsMut<Self::Backend>);

    /// Sets the contents of `self` to the contents of `other`.
    fn set_to(&self, dst: impl AsMut<Self::Backend>, src: impl AsRef<Self::Backend>);

    /// The number of words of type `W` used by a counter.
    fn words_per_counter(&self) -> usize;
}

pub trait MergeCounterLogic<T>: CounterLogic<T> {
    type MergeHelper;

    fn new_merge_helper(&self) -> Self::MergeHelper;

    fn merge_into(&self, dst: impl AsMut<Self::Backend>, src: impl AsRef<Self::Backend>) {
        let mut helper = self.new_merge_helper();
        self.merge_into_with_helper(dst, src, &mut helper);
    }

    fn merge_into_with_helper(
        &self,
        dst: impl AsMut<Self::Backend>,
        src: impl AsRef<Self::Backend>,
        helper: &mut Self::MergeHelper,
    );
}

pub trait Counter<T, C: CounterLogic<T> + MergeCounterLogic<T>> {
    type OwnedCounter: Counter<T, C>;

    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self) -> f64;

    fn as_backend(&self) -> &C::Backend;

    fn new_merge_helper(&self) -> C::MergeHelper;

    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&mut self, element: T);

    /// Clears the counter.
    fn clear(&mut self);

    /// Sets the contents of `self` to the contents of `other`.
    fn set_to(&mut self, other: impl AsRef<C::Backend>);

    fn merge(&mut self, other: impl AsRef<C::Backend>) {
        let mut helper = self.new_merge_helper();
        self.merge_with_helper(other, &mut helper);
    }

    fn merge_with_helper(&mut self, other: impl AsRef<C::Backend>, helper: &mut C::MergeHelper);

    fn as_mut_backend(&mut self) -> &mut C::Backend;

    fn into_owned(self) -> Self::OwnedCounter;
}

pub trait CounterArray<T, C: CounterLogic<T> + MergeCounterLogic<T>> {
    type Counter<'a>: Counter<T, C>
    where
        Self: 'a;

    fn get_counter_logic(&self) -> &C;

    fn get_backend(&self, index: usize) -> &C::Backend;

    unsafe fn set_to(&self, index: usize, content: impl AsRef<C::Backend>);

    fn get_mut_counter(&mut self, index: usize) -> Self::Counter<'_>;

    fn get_backend_mut(&mut self, index: usize) -> &mut C::Backend;

    fn clear(&mut self);
}
