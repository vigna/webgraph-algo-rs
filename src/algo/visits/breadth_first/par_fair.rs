use crate::algo::visits::{breadth_first::*, Parallel};
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::{borrow::Borrow, sync::atomic::Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// Fair parallel breadth-first visits.
///
/// “Fairness” refers to the fact that the visit is parallelized by dividing the
/// visit queue in chunks of approximately equal size; threads consume the
/// chunks, and visit the associated nodes. Thus, the visiting cost is
/// distributed evenly among the threads, albeit the work done on the
/// enumeration of successors depends on the sum of the outdegrees nodes in a
/// chunk, which might differ significantly between chunks.
///
/// There are two version of the visit, which are type aliases to the same
/// common implementation: [`ParFair`] and [`ParFairPred`].
///
/// * [`ParFair`] does not keep track of predecessors; it can be used, for
///   example, to compute distances.
/// * [`ParFairPred`] keeps track of predecessors; it can be used, for example,
///   to compute a visit tree.
///
/// Each type of visit uses incrementally more space:
/// * [`ParFair`] uses one bit per node to remember known nodes and a queue of
///   `usize` representing nodes;
/// * [`ParFairPred`] uses one bit per node to remember known nodes and a queue
///   of pairs of `usize` representing nodes and their parents.
///
/// If you need predecessors but the cost of the callbacks is not significant
/// you can use a [low-memory parallel
/// visit](crate::algo::visits::breadth_first::ParLowMem) instead.
///
/// The visits differ also in the type of events they generate:
/// * [`ParFair`] generates events of type [`Event`].
/// * [`ParFairPred`] generates events of type [`EventPred`].
///
/// With respect to [`Event`], [`EventPred`] provides the predecessor of the
/// current node.
///
/// The progress logger will be updated each time all nodes at a given
/// distance have been processed. This granularity is very low, but it
/// provides more realiable results.
///
/// # Examples
///
/// Let's compute the distances from 0:
///
/// ```
/// use webgraph_algo::algo::visits::Parallel;
/// use webgraph_algo::algo::visits::breadth_first::{*, self};
/// use webgraph_algo::threads;
/// use dsi_progress_logger::no_logging;
/// use webgraph::graphs::vec_graph::VecGraph;
/// use webgraph::labels::proj::Left;
/// use std::sync::atomic::AtomicUsize;
/// use std::sync::atomic::Ordering;
/// use unwrap_infallible::UnwrapInfallible;
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3)]));
/// let mut visit = breadth_first::ParFair::new(&graph, 1);
/// let mut d = [AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0)];
/// visit.visit(
///     0,
///     |event|
///         {
///             // Set distance from 0
///             if let Event::Unknown {curr, distance, ..} = event {
///                 d[curr].store(distance, Ordering::Relaxed);
///             }
///             Ok(())
///         },
///    threads![],
///    no_logging![]
/// ).unwrap_infallible();
/// assert_eq!(d[0].load(Ordering::Relaxed), 0);
/// assert_eq!(d[1].load(Ordering::Relaxed), 1);
/// assert_eq!(d[2].load(Ordering::Relaxed), 2);
/// assert_eq!(d[3].load(Ordering::Relaxed), 2);
/// ```

pub struct ParFairBase<G: RandomAccessGraph, const PRED: bool = false> {
    graph: G,
    granularity: usize,
    visited: AtomicBitVec,
}

/// A fair parallel breadth-first visit that keeps track of its predecessors.
pub type ParFairPred<G> = ParFairBase<G, true>;

/// A fair parallel breadth-first visit.
pub type ParFair<G> = ParFairBase<G, false>;

impl<G: RandomAccessGraph, const P: bool> ParFairBase<G, P> {
    /// Creates a fair parallel breadth-first visit.
    ///
    /// # Arguments
    /// * `graph`: the graph to visit.
    /// * `granularity`: the number of nodes per chunk. High granularity reduces
    ///   overhead, but may lead to decreased performance on graphs with a
    ///   skewed outdegree distribution.
    #[inline(always)]
    pub fn new(graph: G, granularity: usize) -> Self {
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            granularity,
            visited: AtomicBitVec::new(num_nodes),
        }
    }
}

impl<G: RandomAccessGraph + Sync> Parallel<Event> for ParFairBase<G, false> {
    fn visit_filtered<
        E: Send,
        C: Fn(Event) -> Result<(), E> + Sync,
        F: Fn(FilterArgs) -> bool + Sync,
    >(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        thread_pool: impl Borrow<rayon::ThreadPool>,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        if self.visited.get(root, Ordering::Relaxed)
            || !filter(FilterArgs {
                curr: root,
                root,
                distance: 0,
            })
        {
            return Ok(());
        }

        let thread_pool = thread_pool.borrow();
        // We do not provide a capacity in the hope of allocating dynamically
        // space as the frontiers grow.
        let mut curr_frontier = Frontier::with_threads(thread_pool, None);
        let mut next_frontier = Frontier::with_threads(thread_pool, None);

        thread_pool.install(|| {
            curr_frontier.push(root);
        });

        callback(Event::Init { root })?;
        self.visited.set(root, true, Ordering::Relaxed);
        let mut distance = 0;

        while !curr_frontier.is_empty() {
            let distance_plus_one = distance + 1;
            thread_pool.install(|| {
                curr_frontier
                    .par_iter()
                    .chunks(self.granularity)
                    .try_for_each(|chunk| {
                        chunk.into_iter().try_for_each(|&curr| {
                            callback(Event::Unknown {
                                curr,
                                root,
                                distance,
                            })?;
                            self.graph
                                .successors(curr)
                                .into_iter()
                                .try_for_each(|succ| {
                                    let curr = succ;
                                    if filter(FilterArgs {
                                        curr,
                                        root,
                                        distance: distance_plus_one,
                                    }) {
                                        if !self.visited.swap(succ, true, Ordering::Relaxed) {
                                            next_frontier.push(succ);
                                        } else {
                                            callback(Event::Known { curr, root })?;
                                        }
                                    }

                                    Result::<(), E>::Ok(())
                                })?;

                            Result::<(), E>::Ok(())
                        })
                    })
            })?;
            pl.update_with_count(curr_frontier.len());
            distance += 1;
            // Swap the frontiers
            std::mem::swap(&mut curr_frontier, &mut next_frontier);
            // Clear the frontier we will fill in the next iteration
            next_frontier.clear();
        }

        Ok(())
    }

    fn visit_all_filtered<
        E: Send,
        C: Fn(Event) -> Result<(), E> + Sync,
        F: Fn(FilterArgs) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        thread_pool: impl Borrow<rayon::ThreadPool>,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        for node in 0..self.graph.num_nodes() {
            self.visit_filtered(node, &callback, &filter, thread_pool.borrow(), pl)?;
        }

        Ok(())
    }

    fn reset(&mut self) {
        self.visited.fill(false, Ordering::Relaxed);
    }
}

impl<G: RandomAccessGraph + Sync> Parallel<EventPred> for ParFairBase<G, true> {
    fn visit_filtered<
        E: Send,
        C: Fn(EventPred) -> Result<(), E> + Sync,
        F: Fn(<EventPred as super::super::Event>::FilterArgs) -> bool + Sync,
    >(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        thread_pool: impl Borrow<rayon::ThreadPool>,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        if self.visited.get(root, Ordering::Relaxed)
            || !filter(FilterArgsPred {
                curr: root,
                pred: root,
                root,
                distance: 0,
            })
        {
            return Ok(());
        }

        let thread_pool = thread_pool.borrow();
        // We do not provide a capacity in the hope of allocating dynamically
        // space as the frontiers grow.
        let mut curr_frontier = Frontier::with_threads(thread_pool, None);
        let mut next_frontier = Frontier::with_threads(thread_pool, None);

        thread_pool.install(|| {
            curr_frontier.push((root, root));
        });

        callback(EventPred::Init { root })?;
        self.visited.set(root, true, Ordering::Relaxed);
        let mut distance = 0;

        while !curr_frontier.is_empty() {
            let distance_plus_one = distance + 1;
            thread_pool.install(|| {
                curr_frontier
                    .par_iter()
                    .chunks(self.granularity)
                    .try_for_each(|chunk| {
                        chunk.into_iter().try_for_each(|&(curr, pred)| {
                            callback(EventPred::Unknown {
                                curr,
                                pred,
                                root,
                                distance,
                            })?;
                            self.graph
                                .successors(curr)
                                .into_iter()
                                .try_for_each(|succ| {
                                    let (curr, pred) = (succ, curr);
                                    if filter(FilterArgsPred {
                                        curr,
                                        pred,
                                        root,
                                        distance: distance_plus_one,
                                    }) {
                                        if !self.visited.swap(succ, true, Ordering::Relaxed) {
                                            next_frontier.push((curr, pred));
                                        } else {
                                            callback(EventPred::Known { curr, pred, root })?;
                                        }
                                    }

                                    Result::<(), E>::Ok(())
                                })?;

                            Result::<(), E>::Ok(())
                        })
                    })
            })?;
            pl.update_with_count(curr_frontier.len());
            distance += 1;
            // Swap the frontiers
            std::mem::swap(&mut curr_frontier, &mut next_frontier);
            // Clear the frontier we will fill in the next iteration
            next_frontier.clear();
        }

        Ok(())
    }

    fn visit_all_filtered<
        E: Send,
        C: Fn(EventPred) -> Result<(), E> + Sync,
        F: Fn(FilterArgsPred) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        thread_pool: impl Borrow<rayon::ThreadPool>,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        for node in 0..self.graph.num_nodes() {
            self.visit_filtered(node, &callback, &filter, thread_pool.borrow(), pl)?;
        }

        Ok(())
    }

    fn reset(&mut self) {
        self.visited.fill(false, Ordering::Relaxed);
    }
}
