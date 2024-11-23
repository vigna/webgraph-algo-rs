use std::borrow::Borrow;

use impl_tools::autoimpl;
pub trait CounterLogic {
    type Item;
    type Backend: ?Sized;
    type Counter<'a>: Counter<Self>
    where
        Self: 'a;

    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&self, counter: impl AsMut<Self::Backend>, element: impl Borrow<Self::Item>);

    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self, counter: impl AsRef<Self::Backend>) -> f64;

    /// Clears the counter.
    fn clear(&self, counter: impl AsMut<Self::Backend>);

    /// Sets the contents of `self` to the contents of `other`.
    fn set_to(&self, dst: impl AsMut<Self::Backend>, src: impl AsRef<Self::Backend>);

    fn new_counter(&self) -> Self::Counter<'_>;
}

pub trait MergeCounterLogic: CounterLogic {
    type Helper;

    fn new_helper(&self) -> Self::Helper;

    fn merge(&self, dst: impl AsMut<Self::Backend>, src: impl AsRef<Self::Backend>) {
        let mut helper = self.new_helper();
        self.merge_with_helper(dst, src, &mut helper);
    }

    fn merge_with_helper(
        &self,
        dst: impl AsMut<Self::Backend>,
        src: impl AsRef<Self::Backend>,
        helper: &mut Self::Helper,
    );
}

pub trait Counter<C: CounterLogic + ?Sized> {
    type OwnedCounter: Counter<C>;

    fn get_logic(&self) -> &C;
    /// Returns the estimate of the number of distinct elements that have been added
    /// to the counter so far.
    fn count(&self) -> f64;

    /// Adds an element to the counter.
    ///
    /// # Arguments
    ///
    /// * `element`: the element to add.
    fn add(&mut self, element: impl Borrow<C::Item>);

    /// Clears the counter.
    fn clear(&mut self);

    fn as_backend(&self) -> impl AsRef<C::Backend>;

    fn as_backend_mut(&mut self) -> impl AsMut<C::Backend>;

    /// Sets the contents of `self` to the contents of `other`.
    fn set_to(&mut self, other: impl AsRef<C::Backend>);

    fn into_owned(self) -> Self::OwnedCounter;
}

pub trait MergeCounter<C: CounterLogic + MergeCounterLogic + ?Sized>: Counter<C> {
    fn merge(&mut self, other: impl AsRef<C::Backend>) {
        let mut helper = self.get_logic().new_helper();
        self.merge_with_helper(other, &mut helper);
    }

    fn merge_with_helper(&mut self, other: impl AsRef<C::Backend>, helper: &mut C::Helper);
}

pub trait CounterArray<C: CounterLogic + MergeCounterLogic + ?Sized> {
    type Counter<'a>: Counter<C>
    where
        Self: 'a;
    type CounterMut<'a>: Counter<C>
    where
        Self: 'a;

    fn logic(&self) -> &C;

    fn get_counter(&self, index: usize) -> Self::Counter<'_>;

    fn get_counter_mut(&mut self, index: usize) -> Self::CounterMut<'_>;

    fn get_backend(&self, index: usize) -> impl AsRef<C::Backend>;

    fn get_backend_mut(&mut self, index: usize) -> &mut C::Backend;

    unsafe fn set_to(&self, index: usize, content: impl AsRef<C::Backend>);

    fn clear(&mut self);
}
