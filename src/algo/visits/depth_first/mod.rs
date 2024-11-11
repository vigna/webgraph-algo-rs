//! Depth-first visits.
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

/// Types of callback events generated during depth-first visits
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
    /// new tree arc, unless all fields are equal to the root.
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

/// Filter arguments for visits that do not keep track of predecessors.
pub struct FilterArgs {
    /// The current node.
    pub curr: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The depth of the visit, that is, the length of the visit path from the
    /// [root](`Self::root`) to [curr](`Self::curr`).
    pub depth: usize,
}

impl super::Event for Event {
    type FilterArgs = FilterArgs;
}

/// Types of callback events generated during depth-first visits
/// keeping track of parent nodes (and possibly of the visit path).
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
        /// traversing a back arc, and retreating from it. This might be always
        /// false if the visit does not keep track of the visit path.
        on_stack: bool,
    },
    /// The enumeration of the successors of the node has been completed: we are
    /// retreating from a tree arc, unless all node fields are equal to
    /// the root.
    Postvisit {
        /// The current node.
        curr: usize,
        /// The parent of [curr](`EventPred::Postvisit::curr`) in the visit tree.
        pred: usize,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from
        /// the [root](`EventPred::Postvisit::root`) to
        /// [curr](`EventPred::Postvisit::curr`).
        depth: usize,
    },
}

/// Filter arguments for visit that keep track of predecessors.
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

impl super::Event for EventPred {
    type FilterArgs = FilterArgsPred;
}
