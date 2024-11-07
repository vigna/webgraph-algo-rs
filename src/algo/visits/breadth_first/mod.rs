//! Breadth-first visits.
//!
//! Implementations must accept a callback function with argument [`Args`]
//! that will be called when visiting the node.

mod seq;
pub use seq::*;

mod par_fair;
pub use par_fair::*;

mod par_low_mem;
pub use par_low_mem::*;

/// Types of callback events generated during a breadth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Event {
    /// Initialization: all node fields are equal to the root and distance is 0.
    /// This event should be used to set up state at the start of the visit.
    Init,
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all fields or [`Args`] are equal to the root.
    Unknown,
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    ///
    /// Note how in parallel contexts this does not guarantee that the callback
    /// with [`Unknown`](`Event::Unknown`) has already been called.
    Known,
}
pub trait QueueItem: Copy + Send + Sync {
    fn new(curr: usize, pred: usize) -> Self;
    fn curr(&self) -> usize;
    fn pred(&self) -> usize;
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct CurrItem {
    curr: usize,
}

impl QueueItem for CurrItem {
    #[inline(always)]
    fn new(curr: usize, _ignored: usize) -> Self {
        Self { curr }
    }

    #[inline(always)]
    fn curr(&self) -> usize {
        self.curr
    }

    #[inline(always)]
    fn pred(&self) -> usize {
        unimplemented!()
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct CurrPredItem {
    curr: usize,
    pred: usize,
}

impl QueueItem for CurrPredItem {
    #[inline(always)]
    fn new(curr: usize, pred: usize) -> Self {
        Self { curr, pred }
    }

    #[inline(always)]
    fn curr(&self) -> usize {
        self.curr
    }

    #[inline(always)]
    fn pred(&self) -> usize {
        self.pred
    }
}

/// Convenience struct to pass arguments to the callback of a
/// breadth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Args<I: QueueItem> {
    /// The node (and possibly its predecessor) being visited.
    pub item: I,
    /// The root of the current visit tree.
    pub root: usize,
    /// The distance of [node](`Self::node`) from the [root](`Self::root`).
    pub distance: usize,
    /// The event that triggered the callback.
    pub event: Event,
}
