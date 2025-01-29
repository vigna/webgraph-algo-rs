use crate::algo::visits::{
    breadth_first::{EventPred, FilterArgsPred},
    Parallel,
};
use dsi_progress_logger::ConcurrentProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::{prelude::*, ThreadPool};
use std::{
    ops::ControlFlow::{self, Continue},
    sync::atomic::Ordering,
};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// Low-memory parallel breadth-first visits.
///
/// “Low memory” refers to the fact that the visit is parallelized by dividing
/// the visit queue in chunks of approximately equal size, but nodes are visited
/// when they are discovered, rather than when they are extracted from the visit
/// queue. This approach makes unnecessary to store parents in the visit queue,
/// thus reducing the memory usage, even if this visit supports [`EventPred`].
/// However, the visiting cost is distributed unevenly among the threads, as it
/// depends on the sum of the outdegrees of the nodes in a chunk, which might
/// differ significantly between chunks.
///
/// If the cost of the callbacks is significant, you can use a [fair parallel
/// visit](crate::algo::visits::breadth_first::ParFairNoPred) to distribute the
/// visiting cost evenly among the threads.
///
/// # Examples
///
/// Let's compute the breadth-first tree starting from 0:
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
/// use std::ops::ControlFlow::Continue;
/// use no_break::NoBreak;
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3)]));
/// let mut visit = breadth_first::ParLowMem::new(&graph, 1);
/// let mut tree = [AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0)];
/// visit.par_visit(
///     0,
///     |event|
///         {
///             // Store the parent
///             if let EventPred::Unknown {curr, pred, ..} = event {
///                 tree[curr].store(pred, Ordering::Relaxed);
///             }
///             Continue(())
///         },
///    &threads![],
///    no_logging![]
/// ).continue_value_no_break();
///
/// assert_eq!(tree[0].load(Ordering::Relaxed), 0);
/// assert_eq!(tree[1].load(Ordering::Relaxed), 0);
/// assert_eq!(tree[2].load(Ordering::Relaxed), 1);
/// assert_eq!(tree[3].load(Ordering::Relaxed), 1);
/// ```
pub struct ParLowMem<G: RandomAccessGraph> {
    graph: G,
    granularity: usize,
    visited: AtomicBitVec,
}

impl<G: RandomAccessGraph> ParLowMem<G> {
    /// Creates a low-memory parallel breadth-first visit.
    ///
    /// # Arguments
    /// * `graph`: the graph to visit.
    /// * `granularity`: the number of nodes per chunk. High granularity reduces
    ///   overhead, but may lead to decreased performance on graphs with a
    ///   skewed outdegree distribution.
    pub fn new(graph: G, granularity: usize) -> Self {
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            granularity,
            visited: AtomicBitVec::new(num_nodes),
        }
    }
}

impl<G: RandomAccessGraph + Sync> Parallel<EventPred> for ParLowMem<G> {
    fn par_visit_filtered<
        E: Send,
        C: Fn(EventPred) -> ControlFlow<E, ()> + Sync,
        F: Fn(FilterArgsPred) -> bool + Sync,
        P: ConcurrentProgressLog,
    >(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        thread_pool: &ThreadPool,
        pl: &mut P,
    ) -> ControlFlow<E, ()> {
        if self.visited.get(root, Ordering::Relaxed)
            || !filter(FilterArgsPred {
                node: root,
                pred: root,
                root,
                distance: 0,
            })
        {
            return Continue(());
        }

        // We do not provide a capacity in the hope of allocating dyinamically
        // space as the frontiers grow.
        let mut curr_frontier = Frontier::with_threads(thread_pool, None);
        let mut next_frontier = Frontier::with_threads(thread_pool, None);

        thread_pool.install(|| curr_frontier.push(root));

        self.visited.set(root, true, Ordering::Relaxed);
        pl.light_update();
        callback(EventPred::Unknown {
            node: root,
            pred: root,
            root,
            distance: 0,
        })?;

        let mut distance = 1;

        // Visit the connected component
        while !curr_frontier.is_empty() {
            thread_pool.install(|| {
                curr_frontier
                    .par_iter()
                    .chunks(self.granularity)
                    .try_for_each_with(pl.clone(), |pl, chunk| {
                        chunk.into_iter().try_for_each(|&node| {
                            self.graph
                                .successors(node)
                                .into_iter()
                                .try_for_each(|succ| {
                                    let (node, pred) = (succ, node);
                                    if filter(FilterArgsPred {
                                        node,
                                        pred,
                                        root,
                                        distance,
                                    }) {
                                        if !self.visited.swap(succ, true, Ordering::Relaxed) {
                                            pl.light_update();
                                            callback(EventPred::Unknown {
                                                node,
                                                pred,
                                                root,
                                                distance,
                                            })?;
                                            next_frontier.push(succ);
                                        } else {
                                            callback(EventPred::Known { node, pred, root })?;
                                        }
                                    }

                                    Continue(())
                                })
                        })
                    })
            })?;
            distance += 1;
            // Swap the frontiers
            std::mem::swap(&mut curr_frontier, &mut next_frontier);
            // Clear the frontier we will fill in the next iteration
            next_frontier.clear();
        }

        callback(EventPred::Done { root })?;

        Continue(())
    }

    fn par_visit_all_filtered<
        E: Send,
        C: Fn(EventPred) -> ControlFlow<E, ()> + Sync,
        F: Fn(FilterArgsPred) -> bool + Sync,
        P: ConcurrentProgressLog,
    >(
        &mut self,
        callback: C,
        filter: F,
        thread_pool: &ThreadPool,
        pl: &mut P,
    ) -> ControlFlow<E, ()> {
        for node in 0..self.graph.num_nodes() {
            self.par_visit_filtered(node, &callback, &filter, thread_pool, pl)?;
        }

        Continue(())
    }

    fn reset(&mut self) {
        self.visited.fill(false, Ordering::Relaxed);
    }
}
