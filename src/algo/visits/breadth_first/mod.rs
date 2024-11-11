//! Breadth-first visits.
//!
//! Implementations must accept a callback function with argument [`Event`], or
//! [`EventPred`] if the visit keeps track of parent nodes. The associated filter
//! argument types are [`FilterArgs`] and [`FilterArgsPred`], respectively.
//!
//! Note that since [`EventPred`] contains the predecessor of the visited node,
//! all post-initialization visit events can be interpreted as arc events. The
//! only exception are the previsit and postvisit events of the root.

mod seq;
pub use seq::*;

mod par_fair;
pub use par_fair::*;

mod par_low_mem;
pub use par_low_mem::*;

/// Types of callback events generated during breadth-first visits
/// not keeping track of parent nodes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Event {
    /// This event should be used to set up state at the start of the visit.
    ///
    /// Note that this event will not happen if the visit is empty, that
    /// is, if the root has been already visited.
    Init {
        /// The root of the current visit tree, that is, the first node that
        /// will be visited.
        root: usize,
    },
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all node fields are equal to the root.
    Unknown {
        /// The current node.
        curr: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The distance of the current node from the [root](`Event::Unknown::root`).
        distance: usize,
    },
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    ///
    /// Note however that in parallel contexts it might happen that callback
    /// with event [`Unknown`](`Event::Unknown`) has not been called yet by the
    /// thread who discovered the node.
    Known {
        /// The current node.
        curr: usize,
        /// The root of the current visit tree.
        root: usize,
    },
}

/// Filter arguments for visits that do not keep track of predecessors.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct FilterArgs {
    /// The current node.
    pub curr: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The distance of the current node from the [root](`Self::root`).
    pub distance: usize,
}

impl super::Event for Event {
    type FilterArgs = FilterArgs;
}

/// Types of callback events generated during breadth-first visits
/// keeping track of parent nodes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum EventPred {
    /// This event should be used to set up state at the start of the visit.
    ///
    /// Note that this event will not happen if the visit is empty, that
    /// is, if the root has been already visited.
    Init {
        /// The root of the current visit tree, that is, the first node that
        /// will be visited.
        root: usize,
    },
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all node fields are equal to the root.
    Unknown {
        /// The current node.
        curr: usize,
        /// The predecessor of [curr](`EventPred::Unknown::curr`).
        pred: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The distance of the current node from the [root](`EventPred::Unknown::root`).
        distance: usize,
    },
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    ///
    /// Note however that in parallel contexts it might happen that callback
    /// with event [`Unknown`](`Event::Unknown`) has not been called yet by the
    /// thread who discovered the node.
    Known {
        /// The current node.
        curr: usize,
        /// The predecessor of [curr](`EventPred::Known::curr`).
        pred: usize,
        /// The root of the current visit tree.
        root: usize,
    },
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct FilterArgsPred {
    /// The current node.
    pub curr: usize,
    /// The predecessor of [curr](`Self::curr`).
    pub pred: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The distance of the current node from the [root](`Self::root`).
    pub distance: usize,
}

impl super::Event for EventPred {
    type FilterArgs = FilterArgsPred;
}
