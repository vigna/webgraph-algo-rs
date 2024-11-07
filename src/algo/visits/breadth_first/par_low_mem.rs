use crate::algo::visits::{breadth_first, ParVisit};
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::{borrow::Borrow, sync::atomic::Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

use super::{CurrPredItem, QueueItem};

/// A low-memory parallel breadth-first visit.
///
/// “Low memory” refers to the fact that the visit is parallelized by dividing
/// the visit queue in chunks of approximately equal size, but nodes are visited
/// when they are discovered, rather than when they are extracted from the visit
/// queue. This approach makes unnecessary to store the parents of the nodes in
/// the visit queue, thus reducing the memory usage. However, the visiting cost
/// is distributed unevenly among the threads, as it depends on the sum of the
/// outdegrees of the nodes in a chunk, which might differ significantly between
/// chunks.
///
/// If the cost of the callbaks is significant, you can use a [fair parallel
/// visit](crate::algo::visits::breadth_first::ParallelBreadthFirstVisit) to
/// distribute the visiting cost evenly among the threads.
pub struct ParallelBreadthFirstVisitFastCB<
    E,
    G: RandomAccessGraph,
    T: Borrow<rayon::ThreadPool> = rayon::ThreadPool,
> {
    graph: G,
    granularity: usize,
    visited: AtomicBitVec,
    threads: T,
    _phantom: std::marker::PhantomData<E>,
}

impl<E, G: RandomAccessGraph> ParallelBreadthFirstVisitFastCB<E, G, rayon::ThreadPool> {
    /// Creates a low-memory parallel breadth-first visit.
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

impl<E, G: RandomAccessGraph, T: Borrow<rayon::ThreadPool>>
    ParallelBreadthFirstVisitFastCB<E, G, T>
{
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

impl<E: Send, G: RandomAccessGraph + Sync, T: Borrow<rayon::ThreadPool>>
    ParVisit<breadth_first::Args<CurrPredItem>, E> for ParallelBreadthFirstVisitFastCB<E, G, T>
{
    fn visit_filtered<
        C: Fn(&breadth_first::Args<CurrPredItem>) -> Result<(), E> + Sync,
        F: Fn(&breadth_first::Args<CurrPredItem>) -> bool + Sync,
    >(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        let args = breadth_first::Args::<CurrPredItem> {
            item: CurrPredItem::new(root, root),
            root,
            distance: 0,
            event: breadth_first::Event::Unknown,
        };
        if self.visited.get(root, Ordering::Relaxed) || !filter(&args) {
            return Ok(());
        }

        // We do not provide a capacity in the hope of allocating dyinamically
        // space as the frontiers grow.
        let mut curr_frontier = Frontier::with_threads(self.threads.borrow(), None);
        let mut next_frontier = Frontier::with_threads(self.threads.borrow(), None);

        self.threads.borrow().install(|| curr_frontier.push(root));

        self.visited.set(root, true, Ordering::Relaxed);

        callback(&args)?;

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
                                    let args = breadth_first::Args::<CurrPredItem> {
                                        item: CurrPredItem::new(succ, node),
                                        root,
                                        distance,
                                        event: breadth_first::Event::Unknown,
                                    };
                                    if filter(&args) {
                                        if !self.visited.swap(succ, true, Ordering::Relaxed) {
                                            callback(&args)?;
                                            next_frontier.push(succ);
                                        } else {
                                            callback(&breadth_first::Args {
                                                item: CurrPredItem::new(succ, node),
                                                root,
                                                distance,
                                                event: breadth_first::Event::Known,
                                            })?;
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
        C: Fn(&breadth_first::Args<CurrPredItem>) -> Result<(), E> + Sync,
        F: Fn(&breadth_first::Args<CurrPredItem>) -> bool + Sync,
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
