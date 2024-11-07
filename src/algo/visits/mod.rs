//! Visits on graphs.
//!
//! Visits have an type parameter `A` and an error type parameter `E`. They
//! accept a callback function with argument `&A` returning a `Result<(), E>`.
//! If a callback returns an error, the visit will be interrupted;
//! uninterruptible visits should use the
//! [`Infallible`](std::convert::Infallible) error type. Note that an
//! interruption does not necessarily denote an error condition (see, e.g.,
//! [`StoppedWhenDone`]).
//!
//! [Sequential visits](Sequential) are visits that are executed in a single
//! thread, whereas [parallel visits](Parallel) use multiple threads. The
//! signature of callbacks reflects this difference: the callbacks of Sequential
//! visits are `FnMut(&A) -> Result<(), E>`, whereas the callbacks of parallel
//! visits are `Fn(&A) -> Result<(), E> + Sync`, and analogously for the filter
//! functions.
//!
//! In case of interruption sequential visits usually return immediately to the
//! caller, whereas in general parallel visits might need to complete part of
//! their subtasks before returning to the caller.
//!
//! Additionally, implementations accepts a filter function that will be called
//! when a new node is discovered. If the filter returns false, the node will be
//! ignored, that is, not even marked as known. Note that in case of parallel
//! visits the filter might be called multiple times on the same node (and
//! with a different predecessor, if available) due to race conditions.
//!
//! All visits accept also a mutable reference to an implementation of
//! [`ProgressLog`](`dsi_progress_logger::ProgressLog`) to log the progress of
//! the visit: [`ProgressLog::light_update`] will be called when completing the
//! visit of a node. As usual, when passing
//! [`no_logging![]`](dsi_progress_logger::no_logging) the logging code should
//! be optimized away by the compiler.
//!
//! Visit must provide a `reset` method that makes it possible to reuse the
//! visit.

pub mod breadth_first;
pub mod depth_first;

use dsi_progress_logger::ProgressLog;
use thiserror::Error;

#[derive(Error, Debug)]
/// The visit was interrupted.
#[error("The visit was interrupted")]
pub struct Interrupted {}

#[derive(Error, Debug)]
/// The result of the visit was computed without completing the visit; for
/// example, during an acyclicity test a single arc pointing at the visit path
/// is sufficient to compute the result.
#[error("Stopped when done")]
pub struct StoppedWhenDone {}

/// Trait for types usable as arguments for the callbacks in visits
pub trait VisitEventArgs {
    /// The type passed as input to the filter.
    type FilterEventArgs;
}

/// A sequential visit.
///
/// Implementation of this trait must provide the
/// [`visit_filtered`](Sequential::visit_filtered) method, which should perform a
/// visit of a graph starting from a given node, and the
/// [`visit_all_filtered`](Sequential::visit_all_filtered) method, which should
/// perform a visit of the whole graph by starting a visit from each node.
pub trait Sequential<A: VisitEventArgs, E> {
    /// Visits the graph from the specified node.
    ///
    /// # Arguments:
    /// * `root`: The node to start the visit from.
    ///
    /// * `callback`: The callback function.
    ///
    /// * `filter`: The filter function.
    ///
    /// * `pl`: A progress logger.
    fn visit_filtered<C: FnMut(A) -> Result<(), E>, F: FnMut(A::FilterEventArgs) -> bool>(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E>;

    /// Visits the graph from the specified node without a filter.
    ///
    /// The default implementation calls
    /// [`visit_filtered`](Sequential::visit_filtered) with a filter that always
    /// returns true.
    #[inline(always)]
    fn visit<C: FnMut(A) -> Result<(), E>>(
        &mut self,
        root: usize,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        self.visit_filtered(root, callback, |_| true, pl)
    }

    /// Visits the whole graph.
    ///
    /// See [`visit_filtered`](Sequential::visit) for more details.
    fn visit_all_filtered<C: FnMut(A) -> Result<(), E>, F: FnMut(A::FilterEventArgs) -> bool>(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E>;

    /// Visits the whole graph without a filter.
    ///
    /// The default implementation calls
    /// [`visit_all_filtered`](Sequential::visit_all_filtered) with a filter that
    /// always returns true.
    #[inline(always)]
    fn visit_all<C: FnMut(A) -> Result<(), E>>(
        &mut self,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        self.visit_all_filtered(callback, |_| true, pl)
    }

    /// Resets the visit status, making it possible to reuse it.
    fn reset(&mut self);
}

/// A parallel visit.
///
/// Implementation of this trait must provide the
/// [`visit_filtered`](Parallel::visit_filtered) method, which should perform a
/// visit of a graph starting from a given node, and the
/// [`visit_all_filtered`](Parallel::visit_all_filtered) method, which should
/// perform a visit of the whole graph by starting a visit from each node.
pub trait Parallel<A: VisitEventArgs, E> {
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
    /// * `pl`: A progress logger.
    fn visit_filtered<C: Fn(A) -> Result<(), E> + Sync, F: Fn(A::FilterEventArgs) -> bool + Sync>(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E>;

    /// Visits the graph from the specified node without a filter.
    ///
    /// This method just calls
    /// [`visit_filtered`](Parallel::visit_filtered)
    /// with a filter that always returns true.
    #[inline(always)]
    fn visit<C: Fn(A) -> Result<(), E> + Sync>(
        &mut self,
        root: usize,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        self.visit_filtered(root, callback, |_| true, pl)
    }

    /// Visits the whole graph.
    ///
    /// See [`visit`](Parallel::visit_filtered) for more details.
    fn visit_all_filtered<
        C: Fn(A) -> Result<(), E> + Sync,
        F: Fn(A::FilterEventArgs) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E>;

    /// Visits the whole graph without a filter.
    ///
    /// The default implementation calls
    /// [`visit_all_filtered`](Parallel::visit_all_filtered) with a filter that
    /// always returns true.
    #[inline(always)]
    fn visit_all<C: Fn(A) -> Result<(), E> + Sync>(
        &mut self,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        self.visit_all_filtered(callback, |_| true, pl)
    }

    /// Resets the visit status, making it possible to reuse it.
    fn reset(&mut self);
}
