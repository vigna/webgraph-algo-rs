pub mod bfv;
pub mod dfv;

use dsi_progress_logger::ProgressLog;

/// A sequential visit.
///
/// Implementation of this trait must provide the
/// [`visit_from_node`](SeqVisit::visit_from_node) method, which should
/// perform a depth-first visit of a graph starting from a given node, and the
/// [`visit`](SeqVisit::visit) method, which should perform a depth-first
/// visit of the whole graph.
///
/// For each node, the visit should invoke a callback with argument of type
/// `A`. In particular, the callback will be called every time a new node
/// is discovered, every time a node is revisited, and every time the
/// enumeration of the successors of a node is completed. The callback will
/// return a boolean value, and the subsequent behavior of the visit may very
/// depending on the value. The specific behavior can be different for different
/// implementations of this trait.
///
pub trait SeqVisit<A> {
    /// Visits the graph from the specified node.
    ///
    /// # Arguments:
    /// * `root`: The node to start the visit from.
    ///
    /// * `callback`: The callback function.
    ///
    /// * `pl`: A progress logger that implements
    ///   [`dsi_progress_logger::ProgressLog`] may be passed to the method to
    ///   log the progress of the visit. If
    ///   `Option::<dsi_progress_logger::ProgressLogger>::None` is passed,
    ///   logging code should be optimized away by the compiler.
    fn visit_from_node<C: FnMut(A), F: Fn(&A) -> bool>(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    );

    /// Visits the whole graph.
    ///
    /// See [`visit_from_node`](SeqVisit::visit_from_node) for more
    /// details.
    fn visit<C: FnMut(A), F: Fn(&A) -> bool>(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    );

    /// Resets the visit status, making it possible to reuse it.
    fn reset(&mut self);
}

/// A parallel visit.
///
/// Implementation of this trait must provide the
/// [`visit_from_node`](ParVisit::visit_from_node) method, which should
/// perform a depth-first visit of a graph starting from a given node, and the
/// [`visit`](ParVisit::visit) method, which should perform a depth-first
/// visit of the whole graph.
///
/// For each node, the visit should invoke a callback with argument of type
/// `A`. In particular, the callback will be called every time a new node
/// is discovered, every time a node is revisited, and every time the
/// enumeration of the successors of a node is completed. The callback will
/// return a boolean value, and the subsequent behavior of the visit may very
/// depending on the value. The specific behavior can be different for different
/// implementations of this trait.
///
pub trait ParVisit<A> {
    /// Visits the graph from the specified node.
    ///
    /// # Arguments:
    /// * `root`: The node to start the visit from.
    ///
    /// * `callback`: The callback function.
    ///
    /// * `pl`: A progress logger that implements
    ///   [`dsi_progress_logger::ProgressLog`] may be passed to the method to
    ///   log the progress of the visit. If
    ///   `Option::<dsi_progress_logger::ProgressLogger>::None` is passed,
    ///   logging code should be optimized away by the compiler.
    fn visit_from_node<C: Fn(A) + Sync, F: Fn(&A) -> bool + Sync>(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    );

    /// Visits the whole graph.
    ///
    /// See [`visit_from_node`](ParVisit::visit_from_node) for more
    /// details.
    fn visit<C: Fn(A) + Sync, F: Fn(&A) -> bool + Sync>(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    );

    /// Resets the visit status, making it possible to reuse it.
    fn reset(&mut self);
}
