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
//!   not marked as known.
//!
//! - If the event is [Known](`Event::Known`) or
//!   [Completed](`Event::Completed`), the visit will be interrupted.

mod single_thread;
pub use single_thread::*;

/// Types of callback events generated during a depth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Event {
    /// Initialization phase; all node fields are equal to the
    /// root and depth is 0.
    Init,
    /// The node thas just been encountered for the first time.
    Previsit,
    /// The node has been encountered before.
    ///
    /// If support  ed bt the visit, the Boolean value denotes
    /// whether the node is currently on the visit stack.
    Revisit(bool),
    /// The enumeration of the successors of the node has been completed.
    Postvisit,
}

/// Convenience struct to pass arguments to the callback of a
/// depth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Args {
    /// The current node.
    pub curr: usize,
    /// The predecessor of [curr](`Self::curr`); if [event](`Self::event`) is
    /// [Unknown](`Event::Unknown`), this is the parent of [curr](`Self::curr`)
    /// in the visit tree.
    pub pred: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The depth of the visit, that is, the length of the visit path from the [root](`Self::root`) to [curr](`Self::curr`).
    pub depth: usize,
    /// The event that triggered the callback.
    pub event: Event,
}
