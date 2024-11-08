//! Breadth-first visits.
//!
//! Implementations must accept a callback function with argument [`Args`]. The
//! callback must be called at the [start of a visit](Event::Init), [every time
//! a new node is discovered](Event::Unknown), and [every time a known node is
//! rediscovered](Event::Known).
//!
//! Some visits require more additional space (usually, double) to pass
//! predecessors to callbacks (this is the case, e.g., of [`ParFair`]). Since
//! not all algorithms require this information, [`Args`] has a type parameter
//! `D` (for “data”) that can be either [`Node`](super::Node) or
//! [`NodePred`](super::NodePred). The same parameter is used to parameterize
//! visit implementations (see, e.g., [`ParFair`]), so implementations can tune
//! their behavior and space usage to support just `D`.
//!
//! Visit that can always provide the predecessor (e.g., [`Seq`]) use directly
//! `Args<NodePred>`. In general, can tell the fixed choice of `D` of an
//! implementation by looking at the type of the argument of its callbacks.

mod seq;
pub use seq::*;

mod par_fair;
pub use par_fair::*;

mod par_low_mem;
pub use par_low_mem::*;

/// Types of callback events generated during a breadth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Event {
    /// This event should be used to set up state at the start of the visit.
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

/// Type of struct used as input for the filter in breadth-first visits.
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

/// Types of callback events generated during a breadth-first visit
/// keeping track of parent nodes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum EventPred {
    /// This event should be used to set up state at the start of the visit.
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
