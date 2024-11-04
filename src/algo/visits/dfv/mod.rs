//! Depth-first visits.
//!
//! Implementations accept a callback function with argument [`Args`]. The
//! callback will be called every time a new node is discovered, every time a
//! node is revisited, and every time the enumeration of the successors of a
//! node is completed (see [`Event`]).
//!
//! Additionally, implementations might accept a filter function that will be
//! called before invoking the callback. The filter function should return
//! `true` if the callback should be invoked, and `false` otherwise. Moreover,
//! depending on the [event](`Event`) that triggered the callback, when the
//! filter returns false the course of the visit will be altered as follows:
//!
//! - If the event is [Unknown](`Event::Unknown`), the node will be ignored and
//!  not marked as known.
//!
//! - If the event is [Known](`Event::Known`) or [Completed](`Event::Completed`),
//! the visit will be interrupted.

mod single_thread;
pub use single_thread::*;

/// Types of callback events generated during a depth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Event {
    /// The node thas just been encountered for the first time.
    Unknown,
    /// The node has been encountered before.
    ///
    /// If supported bt the visit, the Boolean value denotes
    /// whether the node is currently on the visit stack.
    Known(bool),
    /// The enumeration of the successors of the node has been completed.
    Completed,
}

/// Convenience struct to pass arguments to the callback of a
/// depth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Args {
    /// The node.
    pub node: usize,
    /// The predecessor of [node](`Self::node`); if [event](`Self::event`) is
    /// [Unknown](`Event::Unknown`), this is the parent of [node](`Self::node`)
    /// in the visit tree.
    pub pred: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The depth of the visit, that is, the length of the visit path from the [root](`Self::root`) to [node](`Self::node`).
    pub depth: usize,
    /// The event that triggered the callback.
    pub event: Event,
}
