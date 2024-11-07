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
        data: NodePred,
        root: usize,
        depth: usize,
    },
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all fields or [`Args`] are equal to the root.
    Previsit {
        data: NodePred,
        root: usize,
        depth: usize,
    },
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    ///
    /// If supported by the visit, the Boolean value denotes whether the node is
    /// currently on the visit path, that is, if we are traversing a back arc,
    /// and retreating from it.
    Revisit {
        data: NodePred,
        root: usize,
        depth: usize,
        on_stack: bool,
    },
    /// The enumeration of the successors of the node has been completed: we are
    /// retreating from a tree arc, unless all fields or [`Args`] are equal to
    /// the root.
    Postvisit {
        data: NodePred,
        root: usize,
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
        data: Node,
        root: usize,
        depth: usize,
    },
    /// The node has been encountered for the first time: we are traversing a
    /// new tree arc, unless all fields or [`Args`] are equal to the root.
    Previsit {
        data: Node,
        root: usize,
        depth: usize,
    },
    /// The node has been encountered before: we are traversing a back arc, a
    /// forward arc, or a cross arc.
    ///
    /// If supported by the visit, the Boolean value denotes whether the node is
    /// currently on the visit path, that is, if we are traversing a back arc,
    /// and retreating from it.
    Revisit {
        data: Node,
        root: usize,
        depth: usize,
        on_stack: bool,
    },
}

/// The type of arguments for a depth-first visi
/// keeping track of parent nodes (and possibly of the visit path).
pub type ArgsPred = Args<NodePred, EventPred>;
