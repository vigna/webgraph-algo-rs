//! Depth-first visits.
//!
//! For each node, the visit should invoke a callback with argument of type
//! [`Args`]. In particular, the callback will be called every time a new node
//! is discovered, every time a node is revisited, and every time the
//! enumeration of the successors of a node is completed (see [`Event`]).

mod single_thread;
pub use single_thread::*;

/// Types of callback events generated during a depth-first visit.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Event {
    /// The node thas just been encountered for the first time.
    ///
    /// The color of the node is white, and will become grey
    /// after this event.
    Unknown,
    /// The node has been encountered before.
    ///
    /// The color of the node is grey or black, and will be
    /// unchanged after this event.
    Known,
    /// The enumeration of the successors of the node has been completed.
    ///
    /// The color of the node is grey, and will turn black after this event.
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
