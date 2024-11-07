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

use super::Data;

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
    /// Note however that in parallel contexts it might happen that callback
    /// with event [`Unknown`](`Event::Unknown`) has not been called yet by the
    /// thread who discovered the node.
    Known,
}

/// Arguments for the callback of a breadth-first visit.
///
/// The type parameter `D` can be either [`Node`](super::Node) or
/// [`NodePred`](super::NodePred) (see the [module
/// documentation](super::breadth_first)).
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Args<D: Data> {
    /// The available data, that is, the current node and possibly its
    /// predecessor (if `D` is [`NodePred`](super::NodePred)). When [`event`](`Self::event`) is
    /// [`Unknown`](`Event::Unknown`), the predecessor is the parent of the
    /// current node in the visit tree.
    pub data: D,
    /// The root of the current visit tree.
    pub root: usize,
    /// The distance of the current node from the [root](`Self::root`).
    pub distance: usize,
    /// The event that triggered the callback.
    pub event: Event,
}
