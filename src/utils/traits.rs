use sux::traits::Word;

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
    type Helper;
    fn new_helper(&self) -> Self::Helper;
    fn merge_into(&self, dst: impl AsMut<Self::Backend>, src: impl AsRef<Self::Backend>) {
        let mut helper = self.new_helper();
        self.merge_into_with_helper(dst, src, &mut helper);
    }
    fn merge_into_with_helper(
        &self,
        dst: impl AsMut<Self::Backend>,
        src: impl AsRef<Self::Backend>,
        helper: &mut Self::Helper,
    );
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
pub trait MergeCounter<T>: Counter<T> {
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
