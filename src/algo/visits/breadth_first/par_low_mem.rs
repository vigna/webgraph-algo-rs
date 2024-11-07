use crate::algo::visits::{
    breadth_first::{EventPred, FilterArgsPred},
    Parallel,
};
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::{borrow::Borrow, sync::atomic::Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// A low-memory parallel breadth-first visit.
///
/// “Low memory” refers to the fact that the visit is parallelized by dividing
/// the visit queue in chunks of approximately equal size, but nodes are visited
/// when they are discovered, rather than when they are extracted from the visit
/// queue. This approach makes unnecessary to store distances and parents in the
/// visit queue, thus reducing the memory usage. However, the visiting cost is
/// distributed unevenly among the threads, as it depends on the sum of the
/// outdegrees of the nodes in a chunk, which might differ significantly between
/// chunks.
///
/// If the cost of the callbacks is significant, you can use a [fair parallel
/// visit](crate::algo::visits::breadth_first::ParFair) to
/// distribute the visiting cost evenly among the threads.
///
/// # Examples
///
/// ```
/// use std::convert::Infallible;
/// use webgraph_algo::algo::visits::*;
/// use dsi_progress_logger::no_logging;
/// use webgraph::graphs::vec_graph::VecGraph;
/// use webgraph::labels::proj::Left;
/// use std::sync::atomic::AtomicUsize;
/// use std::sync::atomic::Ordering;
///
/// // Let's compute the distances from 0
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3), (3, 3)]));
/// let mut visit = breadth_first::ParLowMem::<_>::new(&graph, 1);
/// let mut d = [AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0)];
/// visit.visit(
///     0,
///     |args|
///         {
///             // Set distance from 0
///             if let breadth_first::EventPred::Unknown {curr, distance, ..} = args {
///                 d[curr].store(distance, Ordering::Relaxed);
///             }
///             Ok(())
///         },
///    no_logging![]
/// ).unwrap();
/// assert_eq!(d[0].load(Ordering::Relaxed), 0);
/// assert_eq!(d[1].load(Ordering::Relaxed), 1);
/// assert_eq!(d[2].load(Ordering::Relaxed), 2);
/// assert_eq!(d[3].load(Ordering::Relaxed), 2);
/// ```
pub struct ParLowMem<
    G: RandomAccessGraph,
    E = std::convert::Infallible,
    T: Borrow<rayon::ThreadPool> = rayon::ThreadPool,
> {
    graph: G,
    granularity: usize,
    visited: AtomicBitVec,
    threads: T,
    _phantom: std::marker::PhantomData<E>,
}

impl<G: RandomAccessGraph, E> ParLowMem<G, E, rayon::ThreadPool> {
    /// Creates a low-memory parallel breadth-first visit with the [default number of
    /// threads](rayon::ThreadPoolBuilder::num_threads).
    ///
    /// # Arguments
    ///
    /// * `graph`: the graph to visit.
    ///
    /// * `granularity`: the number of nodes per chunk. High granularity reduces
    ///   overhead, but may lead to decreased performance on graphs with a
    ///   skewed outdegree distribution.
    pub fn new(graph: G, granularity: usize) -> Self {
        Self::with_num_threads(graph, granularity, 0)
    }

    /// Creates a low-memory parallel top-down visit that uses the specified number of threads.
    ///
    /// # Arguments
    ///
    /// * `graph`: the graph to visit.
    ///
    /// * `granularity`: the number of nodes per chunk. High granularity reduces
    ///   overhead, but may lead to decreased performance on graphs with a
    ///   skewed outdegree distribution.
    ///
    /// * `num_threads`: the number of threads to use.
    pub fn with_num_threads(graph: G, granularity: usize, num_threads: usize) -> Self {
        let threads = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .unwrap_or_else(|_| panic!("Could not build threadpool with {} threads", num_threads));
        Self::with_threads(graph, granularity, threads)
    }
}

impl<G: RandomAccessGraph, E, T: Borrow<rayon::ThreadPool>> ParLowMem<G, E, T> {
    /// Creates a low-memory parallel top-down visit that uses the specified number of threads.
    ///
    /// # Arguments
    ///
    /// * `graph`: the graph to visit.
    ///
    /// * `granularity`: the number of nodes per chunk. High granularity reduces
    ///   overhead, but may lead to decreased performance on graphs with a
    ///   skewed outdegree distribution.
    ///
    /// * `threads`: a thread pool.
    pub fn with_threads(graph: G, granularity: usize, threads: T) -> Self {
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            granularity,
            visited: AtomicBitVec::new(num_nodes),
            threads,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<G: RandomAccessGraph + Sync, E: Send, T: Borrow<rayon::ThreadPool>> Parallel<EventPred, E>
    for ParLowMem<G, E, T>
{
    fn visit_filtered<
        C: Fn(EventPred) -> Result<(), E> + Sync,
        F: Fn(FilterArgsPred) -> bool + Sync,
    >(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
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

        // We do not provide a capacity in the hope of allocating dyinamically
        // space as the frontiers grow.
        let mut curr_frontier = Frontier::with_threads(self.threads.borrow(), None);
        let mut next_frontier = Frontier::with_threads(self.threads.borrow(), None);

        self.threads.borrow().install(|| curr_frontier.push(root));

        self.visited.set(root, true, Ordering::Relaxed);

        callback(EventPred::Unknown {
            curr: root,
            pred: root,
            root,
            distance: 0,
        })?;

        let mut distance = 1;

        // Visit the connected component
        while !curr_frontier.is_empty() {
            self.threads.borrow().install(|| {
                curr_frontier
                    .par_iter()
                    .chunks(self.granularity)
                    .try_for_each(|chunk| {
                        chunk.into_iter().try_for_each(|&node| {
                            self.graph
                                .successors(node)
                                .into_iter()
                                .try_for_each(|succ| {
                                    let (curr, pred) = (succ, node);
                                    if filter(FilterArgsPred {
                                        curr,
                                        pred,
                                        root,
                                        distance,
                                    }) {
                                        if !self.visited.swap(succ, true, Ordering::Relaxed) {
                                            callback(EventPred::Unknown {
                                                curr,
                                                pred,
                                                root,
                                                distance,
                                            })?;
                                            next_frontier.push(succ);
                                        } else {
                                            callback(EventPred::Known { curr, pred, root })?;
                                        }
                                    }

                                    Result::<(), E>::Ok(())
                                })
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
        C: Fn(EventPred) -> Result<(), E> + Sync,
        F: Fn(FilterArgsPred) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        for node in 0..self.graph.num_nodes() {
            self.visit_filtered(node, &callback, &filter, pl)?;
        }

        Ok(())
    }

    fn reset(&mut self) {
        self.visited.fill(false, Ordering::Relaxed);
    }
}
