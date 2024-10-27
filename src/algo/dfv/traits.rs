use dsi_progress_logger::ProgressLog;

/// Types of callback events generated during a [`DepthFirstVisit`].
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
/// [`DepthFirstVisit`].
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct DFVArgs {
    /// The node.
    pub node: usize,
    /// The predecessor of [node](`Self::node`); if [event](`Self::event`) is
    /// [Unknown](`Event::Unknown`), this is the parent of [node](`Self::node`)
    /// in the visit tree.
    pub pred: usize,
    /// The root of the current visit tree.
    pub root: usize,
    /// The distance of [node](`Self::node`) from the [root](`Self::root`).
    pub distance: usize,
    /// The event that triggered the callback.
    pub event: Event,
}

/// Depth-first visits for a graph.
///
/// Implementation of this trait must provide the
/// [`visit_from_node`](DepthFirstVisit::visit_from_node) method, which should
/// perform a depth-first visit of a graph starting from a given node, and the
/// [`visit`](DepthFirstVisit::visit) method, which should perform a depth-first
/// visit of the whole graph.
///
/// For each node, the visit should invoke a callback with argument of type
/// [`DFVArgs`]. In particular, the callback will be called every time a new node
/// is discovered, every time a node is revisited, and every time the
/// enumeration of the successors of a node is completed. The callback will
/// return a boolean value, and the subsequent behavior of the visit may very
/// depending on the value. The specific behavior can be different for different
/// implementations of this trait.
///
pub trait DepthFirstVisit {
    /// Visits depth-first the graph from the specified node.
    ///
    /// # Arguments:
    /// * `callback`: The callback function.
    ///
    /// * `root`: The node to start the visit from.
    ///
    /// * `pl`: A progress logger that implements
    ///   [`dsi_progress_logger::ProgressLog`] may be passed to the method to
    ///   log the progress of the visit. If
    ///   `Option::<dsi_progress_logger::ProgressLogger>::None` is passed,
    ///   logging code should be optimized away by the compiler.
    fn visit_from_node(
        &mut self,
        callback: impl Fn(DFVArgs) -> bool + Sync,
        root: usize,
        pl: &mut impl ProgressLog,
    );

    /// Visits the whole graph.
    fn visit(&mut self, callback: impl Fn(DFVArgs) -> bool + Sync, pl: &mut impl ProgressLog);

    /// Resets the visit status, making it possible to reuse it.
    fn reset(&mut self);
}
