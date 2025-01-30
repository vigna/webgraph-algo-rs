/*
 * SPDX-FileCopyrightText: 2024 Matteo Dell'Acqua
 * SPDX-FileCopyrightText: 2025 Sebastiano Vigna
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

//! Visits on graphs.
//!
//! Implementation of [sequential](Sequential) and [parallel][Parallel] visits
//! depend on a type parameter `A` implementing the trait [`Event`]; they
//! provide visit methods accepting a callback function with argument `A` and
//! returning a `ControlFlow<E, ()>`, where `E` is a type parameter of the visit
//! method: for example, `E` might be [`StoppedWhenDone`] when completing early,
//! [`Interrupted`] when interrupted or [`Infallible`](std::convert::Infallible)
//! if the visit cannot be interrupted.
//!
//! If a callback returns [`Break`](ControlFlow::Break), the visit will be
//! interrupted, and the interrupt propagated to the caller of the visit method;
//! for uninterruptible visits we suggest to use the
//! [`no-break`](https://crates.io/crates/no-break) crate and its
//! [`continue_value_no_break`](no_break::NoBreak::continue_value_no_break)
//! method on the result to let type inference run smoothly.
//!
//! Note that an interruption does not necessarily denote an error condition
//! (see, e.g., [`StoppedWhenDone`]).
//!
//! [Sequential visits](Sequential) are visits that are executed in a single
//! thread, whereas [parallel visits](Parallel) use multiple threads. The
//! signature of callbacks reflects this difference: the callbacks of sequential
//! visits are `FnMut(A) -> ControlFlow<E, ()>`, whereas the callbacks of
//! parallel visits are `Fn(A) -> ControlFlow<E, ()> + Sync`.
//!
//! In case of interruption sequential visits usually return immediately to the
//! caller, whereas in general parallel visits might need to complete part of
//! their subtasks before returning to the caller.
//!
//! Additionally, implementations might accepts a filter function accepting a
//! [`Event::FilterArgs`] that will be called when a new node is discovered. If
//! the filter returns false, the node will be ignored, that is, not even marked
//! as known. Note that in case of parallel visits the filter might be called
//! multiple times on the same node (and with a different predecessor, if
//! available) due to race conditions.
//!
//! All visits accept also a mutable reference to an implementation of
//! [`ProgressLog`](`dsi_progress_logger::ProgressLog`) or
//! [`ConcurrentProgressLog`](`dsi_progress_logger::ConcurrentProgressLog`) to
//! log the progress of the visit: [`ProgressLog::light_update`] will be called
//! just before invoking the callback on a node-discovery event (`Previsit` for
//! depth-first visits, `Unknown` for breadth-first visits). As usual, when
//! passing [`no_logging![]`](dsi_progress_logger::no_logging) the logging code
//! should be optimized away by the compiler.
//!
//! There is a blanket implementation of the [`Parallel`] trait for all types
//! implementing the [`Sequential`] trait. This approach makes it possible to
//! have structures that can use both sequential and parallel visits.
//!
//! Visit must provide a `reset` method that makes it possible to reuse the
//! visit.

pub mod breadth_first;
pub mod depth_first;

use dsi_progress_logger::{ConcurrentProgressLog, ProgressLog};
use rayon::ThreadPool;
use std::ops::ControlFlow;
use thiserror::Error;

#[derive(Error, Debug)]
/// The visit was interrupted.
#[error("The visit was interrupted")]
pub struct Interrupted;

#[derive(Error, Debug)]
/// The result of the visit was computed without completing the visit; for
/// example, during an acyclicity test a single arc pointing at the visit path
/// is sufficient to compute the result.
#[error("Stopped when done")]
pub struct StoppedWhenDone;

/// Types usable as arguments for the callbacks in visits.
///
/// Arguments are usually enums in which variants represent visit events
/// (previsits, postvisits, etc.). Each variant then contains additional data
/// related to the specific event.
///
/// The associated type [`Event::FilterArgs`] is the type of the arguments
/// passed to the filter associated with the visit. It can be set to `()` if
/// filtering is not supported
pub trait Event {
    /// The type passed as input to the filter.
    type FilterArgs;
}

/// A convenience type alias for the filter arguments of an event.
///
/// It is useful to write match patterns using destructuring syntax.
pub type FilterArgs<A> = <A as Event>::FilterArgs;

/// A sequential visit.
///
/// Implementation of this trait must provide the
/// [`visit_filtered`](Sequential::visit_filtered) method, which should perform a
/// visit of a graph starting from a given node, and the
/// [`visit_all_filtered`](Sequential::visit_all_filtered) method, which should
/// perform a visit of the whole graph by starting a visit from each node.
pub trait Sequential<A: Event> {
    /// Visits the graph from the specified node.
    ///
    /// # Arguments:
    /// * `root`: The node to start the visit from.
    /// * `callback`: The callback function.
    /// * `filter`: The filter function.
    /// * `pl`: A progress logger.
    fn visit_filtered<
        R: IntoIterator<Item = usize>,
        E,
        C: FnMut(A) -> ControlFlow<E, ()>,
        F: FnMut(A::FilterArgs) -> bool,
        P: ProgressLog,
    >(
        &mut self,
        roots: R,
        callback: C,
        filter: F,
        pl: &mut P,
    ) -> ControlFlow<E, ()>;

    /// Visits the graph from the specified node without a filter.
    ///
    /// The default implementation calls
    /// [`visit_filtered`](Sequential::visit_filtered) with a filter that always
    /// returns true.
    #[inline(always)]
    fn visit<
        R: IntoIterator<Item = usize>,
        E,
        C: FnMut(A) -> ControlFlow<E, ()>,
        P: ProgressLog,
    >(
        &mut self,
        root: R,
        callback: C,
        pl: &mut P,
    ) -> ControlFlow<E, ()> {
        self.visit_filtered(root, callback, |_| true, pl)
    }

    /// Resets the visit status, making it possible to reuse it.
    fn reset(&mut self);
}

/// A parallel visit.
///
/// Implementation of this trait must provide the
/// [`visit_filtered`](Parallel::par_visit_filtered) method, which should perform a
/// visit of a graph starting from a given node, and the
/// [`visit_all_filtered`](Parallel::par_visit_all_filtered) method, which should
/// perform a visit of the whole graph by starting a visit from each node.
pub trait Parallel<A: Event> {
    /// Visits the graph from the specified node.
    ///
    /// # Arguments:
    /// * `root`: The node to start the visit from.
    /// * `callback`: The callback function.
    /// * `filter`: A filter function that will be called on each node to
    ///    determine whether the node should be visited or not.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    fn par_visit_filtered<
        R: IntoIterator<Item = usize>,
        E: Send,
        C: Fn(A) -> ControlFlow<E, ()> + Sync,
        F: Fn(A::FilterArgs) -> bool + Sync,
        P: ConcurrentProgressLog,
    >(
        &mut self,
        roots: R,
        callback: C,
        filter: F,
        thread_pool: &ThreadPool,
        pl: &mut P,
    ) -> ControlFlow<E, ()>;

    /// Visits the graph from the specified node without a filter.
    ///
    /// This method just calls
    /// [`visit_filtered`](Parallel::par_visit_filtered)
    /// with a filter that always returns true.
    #[inline(always)]
    fn par_visit<
        R: IntoIterator<Item = usize>,
        E: Send,
        C: Fn(A) -> ControlFlow<E, ()> + Sync,
        P: ConcurrentProgressLog,
    >(
        &mut self,
        roots: R,
        callback: C,
        thread_pool: &ThreadPool,
        pl: &mut P,
    ) -> ControlFlow<E, ()> {
        self.par_visit_filtered(roots, callback, |_| true, thread_pool, pl)
    }

    /// Resets the visit status, making it possible to reuse it.
    fn reset(&mut self);
}
