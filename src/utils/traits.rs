pub trait CounterLogic<T> {
    type Helper;
    type Backend: ?Sized + PartialEq;

    fn new_helper(&self) -> Self::Helper;

    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&self, counter: &mut Self::Backend, element: T);

    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self, counter: &Self::Backend) -> f64;

    /// Clears the counter.
    fn clear(&self, counter: &mut Self::Backend);

    /// Sets the contents of `self` to the contents of `other`.
    fn set_to(&self, dst: &mut Self::Backend, src: &Self::Backend);

    /// The number of words of type `W` used by a counter.
    fn words_per_counter(&self) -> usize;
}

pub trait MergeCounterLogic<T>: CounterLogic<T> {
    fn merge_into(&self, dst: &mut Self::Backend, src: &Self::Backend) {
        let mut helper = self.new_helper();
        self.merge_into_with_helper(dst, src, &mut helper);
    }
    fn merge_into_with_helper(
        &self,
        dst: &mut Self::Backend,
        src: &Self::Backend,
        helper: &mut Self::Helper,
    );
}

pub trait ImmutableCounter<T, C: CounterLogic<T>> {
    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self) -> f64;

    fn as_backend(&self) -> &C::Backend;

    fn new_helper(&self) -> C::Helper;
}

pub trait MutableCounter<T, C: CounterLogic<T>>: ImmutableCounter<T, C> {
    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&mut self, element: T);

    /// Clears the counter.
    fn clear(&mut self);

    /// Sets the contents of `self` to the contents of `other`.
    fn set_to(&mut self, other: &C::Backend);

    fn merge(&mut self, other: &C::Backend) {
        let mut helper = self.new_helper();
        self.merge_with_helper(other, &mut helper);
    }

    fn merge_with_helper(&mut self, other: &C::Backend, helper: &mut C::Helper);

    fn as_mut_backend(&mut self) -> &mut C::Backend;
}

pub trait CounterArray<T, C: CounterLogic<T>> {
    type SharedCounter<'a>: ImmutableCounter<T, C>
    where
        Self: 'a;
    type MutCounter<'a>: MutableCounter<T, C>
    where
        Self: 'a;
    type OwnedCounter: MutableCounter<T, C>;

    fn get_counter_logic(&self) -> &C;

    fn get_counter(&self, index: usize) -> Self::SharedCounter<'_>;

    unsafe fn get_mut_counter_unsafe(&self, index: usize) -> Self::MutCounter<'_>;

    fn get_owned_counter(&self, index: usize) -> Self::OwnedCounter;

    fn get_backend(&self, index: usize) -> &C::Backend;

    unsafe fn get_backend_mut_unsafe(&self, index: usize) -> &mut C::Backend;

    #[inline(always)]
    fn get_mut_counter(&mut self, index: usize) -> Self::MutCounter<'_> {
        unsafe {
            // Safety: we have a mut ref
            self.get_mut_counter_unsafe(index)
        }
    }

    #[inline(always)]
    fn get_backend_mut(&mut self, index: usize) -> &mut C::Backend {
        unsafe {
            // Safety: we have a mut ref
            self.get_backend_mut_unsafe(index)
        }
    }

    fn clear(&mut self);
}
