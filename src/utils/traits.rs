use std::borrow::Borrow;

pub trait CounterLogic {
    type Item;
    type Backend: ?Sized;
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

    fn new_counter(&self) -> Self::Counter<'_>;
}

pub trait MergeCounterLogic: CounterLogic {
    type Helper;

    fn new_helper(&self) -> Self::Helper;

    fn merge(&self, dst: &mut Self::Backend, src: &Self::Backend) {
        let mut helper = self.new_helper();
        self.merge_with_helper(dst, src, &mut helper);
    }

    fn merge_with_helper(
        &self,
        dst: &mut Self::Backend,
        src: &Self::Backend,
        helper: &mut Self::Helper,
    );
}

pub trait Counter<C: CounterLogic + ?Sized> {
    type OwnedCounter: Counter<C>;

    fn get_logic(&self) -> &C;
    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self) -> f64;

    fn as_backend(&self) -> &C::Backend;

    fn into_owned(self) -> Self::OwnedCounter;
}

pub trait CounterMut<C: CounterLogic + ?Sized>: Counter<C> {
    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&mut self, element: impl Borrow<C::Item>);

    /// Clears the counter.
    fn clear(&mut self);

    fn as_backend_mut(&mut self) -> &mut C::Backend;

    /// Sets the contents of `self` to the contents of `other`.
    fn set(&mut self, other: &C::Backend);
}

pub trait MergeCounter<L: MergeCounterLogic + ?Sized>: CounterMut<L> {
    fn merge(&mut self, other: &L::Backend) {
        let mut helper = self.get_logic().new_helper();
        self.merge_with_helper(other, &mut helper);
    }

    fn merge_with_helper(&mut self, other: &L::Backend, helper: &mut L::Helper);
}

pub trait CounterArray<C: CounterLogic + ?Sized> {
    type Counter<'a>: Counter<C>
    where
        Self: 'a;

    fn logic(&self) -> &C;

    fn get_counter(&self, index: usize) -> Self::Counter<'_>;

    fn get_backend(&self, index: usize) -> &C::Backend;
}

pub trait CounterArrayMut<L: MergeCounterLogic + ?Sized>: CounterArray<L> {
    type CounterMut<'a>: CounterMut<L>
    where
        Self: 'a;

    fn get_counter_mut(&mut self, index: usize) -> Self::CounterMut<'_>;

    fn get_backend_mut(&mut self, index: usize) -> &mut L::Backend;

    /// Sets the contents of the counter at `index` to `content`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `content` has the same length as the counter
    /// at `index`. The caller must ensure that there are no data races.
    unsafe fn set(&self, index: usize, content: &L::Backend);

    fn clear(&mut self);
}
