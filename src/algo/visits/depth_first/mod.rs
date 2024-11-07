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

use super::{Node, NodePred};

/// Types of callback events generated during a depth-first visit
/// not keeping track of parent nodes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Event {
    /// Initialization: all node fields are equal to the root and depth is 0.
    /// This event should be used to set up state at the start of the visit.
    Init,
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all fields or [`Args`] are equal to the root.
    Previsit,
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    Revisit,
}

/// Types of callback events generated during a depth-first visit
/// keeping track of parent nodes (and possibly of the visit path).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum EventPred {
    /// Initialization: all node fields are equal to the root and depth is 0.
    /// This event should be used to set up state at the start of the visit.
    Init {
        /// The available data, that is, the current node and its predecessor.
        data: NodePred,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`EventPred::Init::root`) to [curr](`EventPred::Init::curr`).
        depth: usize,
    },
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all fields or [`Args`] are equal to the root.
    Previsit {
        /// The available data, that is, the current node and its predecessor.
        data: NodePred,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`EventPred::Previsit::root`) to [curr](`EventPred::Previsit::curr`).
        depth: usize,
    },
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    Revisit {
        /// The available data, that is, the current node and its predecessor.
        data: NodePred,
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
        /// The available data, that is, the current node and its predecessor.
        data: NodePred,
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
        /// The available data, that is, the current node.
        data: Node,
        /// The root of the current visit tree.
        root: usize,
        depth: usize,
    },
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all fields or [`Args`] are equal to the root.
    Previsit {
        /// The available data, that is, the current node.
        data: Node,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`Event::Previsit::root`) to [curr](`Event::Previsit::curr`).
        depth: usize,
    },
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    ///
    /// If supported by the visit, the Boolean value denotes whether the node is
    /// currently on the visit path, that is, if we are traversing a back arc,
    /// and retreating from it.
    Revisit {
        /// The available data, that is, the current node.
        data: Node,
        /// The root of the current visit tree.
        root: usize,
        /// The depth of the visit, that is, the length of the visit path from the
        /// [root](`Event::Revisit::root`) to [curr](`Event::Revisit::curr`).
        depth: usize,
        /// Whether the node is currently on the visit path, that is, if we are
        /// traversing a back arc, and retreating from it.
        on_stack: bool,
    },
}

/// The type of arguments for a depth-first visi
/// keeping track of parent nodes (and possibly of the visit path).
pub type ArgsPred = Args<NodePred, EventPred>;
