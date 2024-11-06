//! Module containing traits and implementations of both depth-first and breadth-first
//! visits on graphs.
//!
//! Breadth-first visits come in 3 flavours:
//! * [`Sequential`](bfv::SingleThreadedBreadthFirstVisit): a single threaded visit.
//! * [`Parallel`](bfv::ParallelBreadthFirstVisit): a parallel visit where at each iteration
//!   the frontier is divided in chunks for the threads in order to call the callback and perform
//!   the visit logic. In order to do so both the node and its parent must be enqued in the frontier.
//! * [`Parallel with fast callbacks`](bfv::ParallelBreadthFirstVisitFastCB): a parallel visit where the
//!   callback is called during successor enumeration, allowing to store only the nodes without their parents.
//!   This leads to slowdowns and less parallelization in the case where the callback is not trascurable relative
//!   to the visit logic but to performance improvements in case it is.

pub mod breadth_first;
pub mod depth_first;

use dsi_progress_logger::ProgressLog;
use thiserror::Error;

#[derive(Error, Debug)]
/// The visit was interrupted.
#[error("The visit was interrupted")]
pub struct Interrupted {}

#[derive(Error, Debug)]
/// This error is returned by visit which can complete their computation
/// without completing the visit (“stop when done”).
#[error("Stopped when done")]
pub struct StoppedWhenDone {}

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
pub trait SeqVisit<A, E> {
    /// Visits the graph from the specified node.
    ///
    /// This method just calls
    /// [`visit_from_node_filtered`](SeqVisit::visit_from_node_filtered)
    /// with a filter that always returns `true`.
    fn visit_from_node<C: FnMut(&A) -> Result<(), E>>(
        &mut self,
        root: usize,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        self.visit_from_node_filtered(root, callback, |_| true, pl)
    }

    /// Visits the graph from the specified node.
    ///
    /// # Arguments:
    /// * `root`: The node to start the visit from.
    ///
    /// * `callback`: The callback function.
    ///
    /// * `filter`: A filter function that will be called on each node to
    ///    determine whether the node should be visited or not.
    ///
    /// * `pl`: A progress logger that implements
    ///   [`dsi_progress_logger::ProgressLog`] may be passed to the method to
    ///   log the progress of the visit. If
    ///   `Option::<dsi_progress_logger::ProgressLogger>::None` is passed,
    ///   logging code should be optimized away by the compiler.
    fn visit_from_node_filtered<C: FnMut(&A) -> Result<(), E>, F: FnMut(&A) -> bool>(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E>;

    /// Visits the whole graph.
    ///
    /// See [`visit_from_node`](SeqVisit::visit_from_node) for more
    /// details.
    fn visit<C: FnMut(&A) -> Result<(), E>, F: FnMut(&A) -> bool>(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E>;

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
pub trait ParVisit<A, E> {
    /// Visits the graph from the specified node.
    ///
    /// This method just calls
    /// [`visit_from_node_filtered`](ParVisit::visit_from_node_filtered)
    /// with a filter that always returns `true`.
    #[inline(always)]
    fn visit_from_node<C: Fn(&A) -> Result<(), E> + Sync>(
        &mut self,
        root: usize,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        self.visit_from_node_filtered(root, callback, |_| true, pl)
    }

    /// Visits the graph from the specified node.
    ///
    /// # Arguments:
    /// * `root`: The node to start the visit from.
    ///
    /// * `callback`: The callback function.
    ///
    /// * `filter`: A filter function that will be called on each node to
    ///    determine whether the node should be visited or not.
    ///
    /// * `pl`: A progress logger that implements
    ///   [`dsi_progress_logger::ProgressLog`] may be passed to the method to
    ///   log the progress of the visit. If
    ///   `Option::<dsi_progress_logger::ProgressLogger>::None` is passed,
    ///   logging code should be optimized away by the compiler.
    fn visit_from_node_filtered<C: Fn(&A) -> Result<(), E> + Sync, F: Fn(&A) -> bool + Sync>(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E>;

    /// Visits the whole graph.
    ///
    /// See [`visit_from_node`](ParVisit::visit_from_node) for more
    /// details.
    fn visit<C: Fn(&A) -> Result<(), E> + Sync, F: Fn(&A) -> bool + Sync>(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E>;

    /// Resets the visit status, making it possible to reuse it.
    fn reset(&mut self);
}
