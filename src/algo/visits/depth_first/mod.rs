//! Depth-first visits.
//!
//! Implementations must accept a callback function with argument [`Args`]. The
//! callback must be called at the [start of a visit](Event::Init), [every time
//! a new node is discovered](Event::Previsit), [every time a node is
//! revisited](Event::Revisit), and, if supported, [every time the enumeration
//! of the successors of a node is completed](EventPred::Postvisit).
//!
//! Note that since [`Args`] contains the predecessor of the visited node, all
//! post-start visit events can be interpreted as arc events. The only exception
//! are the previsit and postvisit events of the root.

mod seq;
pub use seq::*;

use super::VisitEventArgs;

/// Types of callback events generated during a depth-first visit
/// keeping track of parent nodes (and possibly of the visit path).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum EventPred {
    /// Initialization: all node fields are equal to the root and depth is 0.
    /// This event should be used to set up state at the start of the visit.
    Init {
        /// The current node.
        curr: usize,
        /// The parent of [curr](`EventPred::Init::curr`) in the visit tree.
        pred: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`EventPred::Init::root`) to [curr](`EventPred::Init::curr`).
        depth: usize,
    },
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all fields or [`Args`] are equal to the root.
    Previsit {
        /// The current node.
        curr: usize,
        /// The parent of [curr](`EventPred::Previsit::curr`) in the visit tree.
        pred: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`EventPred::Previsit::root`) to [curr](`EventPred::Previsit::curr`).
        depth: usize,
    },
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    Revisit {
        /// The current node.
        curr: usize,
        /// The parent of [curr](`EventPred::Revisit::curr`) in the visit tree.
        pred: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`EventPred::Revisit::root`) to [curr](`EventPred::Revisit::curr`).
        depth: usize,
        /// Whether the node is currently on the visit path, that is, if we are
        /// traversing a back arc, and retreating from it.
        on_stack: bool,
    },
    /// The enumeration of the successors of the node has been completed: we are
    /// retreating from a tree arc, unless all fields or [`Args`] are equal to
    /// the root.
    Postvisit {
        /// The current node.
        curr: usize,
        /// The parent of [curr](`EventPred::Postvisit::curr`) in the visit tree.
        pred: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`EventPred::Postvisit::root`) to [curr](`EventPred::Postfisit::curr`).
        depth: usize,
    },
}

/// Types of callback events generated during a depth-first visit
/// not keeping track of parent nodes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Event {
    /// Initialization: all node fields are equal to the root and depth is 0.
    /// This event should be used to set up state at the start of the visit.
    Init {
        /// The current node.
        curr: usize,
        /// The root of the current visit tree.
        root: usize,
        depth: usize,
    },
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all fields or [`Args`] are equal to the root.
    Previsit {
        /// The current node.
        curr: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`Event::Previsit::root`) to [curr](`Event::Previsit::curr`).
        depth: usize,
    },
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    Revisit {
        /// The current node.
        curr: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`Event::Revisit::root`) to [curr](`Event::Revisit::curr`).
        depth: usize,
    },
}

pub struct FilterArgs {
    /// The current node.
    pub curr: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The depth of the visit, that is, the length of the visit path from the
    /// [root](`Self::root`) to [curr](`Self::curr`).
    pub depth: usize,
}

/// Type of struct used as input for the filter in depth-first visits.
pub struct FilterArgsPred {
    /// The current node.
    pub curr: usize,
    /// The parent of [curr](`Self::curr`) in the visit tree.
    pub pred: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The depth of the visit, that is, the length of the visit path from the
    /// [root](`Self::root`) to [curr](`Self::curr`).
    pub depth: usize,
}

impl VisitEventArgs for Event {
    type FilterEventArgs = FilterArgs;
}

impl VisitEventArgs for EventPred {
    type FilterEventArgs = FilterArgsPred;
}
