//! Breadth-first visits.
//!
//! For each node, the visit should invoke a callback with argument of type
//! [`Args`] when the node is visited.

mod seq;
pub use seq::*;

mod par_fair;
pub use par_fair::*;

mod par_low_mem;
pub use par_low_mem::*;

/// Convenience struct to pass arguments to the callback of a
/// breadth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Args {
    /// The node.
    pub node: usize,
    /// The parent of [node](`Self::node`) in the visit tree.
    pub parent: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The distance of [node](`Self::node`) from the [root](`Self::root`).
    pub distance: usize,
}
