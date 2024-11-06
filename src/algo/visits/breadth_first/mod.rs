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

/// Convenience struct to pass arguments to the callback of a
/// breadth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Args {
    /// The node.
    pub curr: usize,
    /// The parent of [node](`Self::node`) in the visit tree.
    pub parent: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The distance of [node](`Self::node`) from the [root](`Self::root`).
    pub distance: usize,
}
