use crate::algo::visits::{breadth_first, ParVisit};
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::{borrow::Borrow, sync::atomic::Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

use super::{Args, QueueItem};

/// A fair parallel breadth-first visit.
///
/// “Fairness” refers to the fact that the visit is parallelized by dividing the
/// visit queue in chunks of approximately equal size; threads consume the
/// chunks, and visit the associated nodes. Thus, the visiting cost is
/// distributed evenly among the threads, albeit the work done on the
/// enumeration of successors depends on the sum of the outdegrees nodes in a
/// chunk, which might differ significantly between chunks.
///
/// If the cost of the callbacks is not significant, you can use a [low-memory
/// parallel
/// visit](crate::algo::visits::breadth_first::ParallelBreadthFirstVisitFastCB)
/// to reduce the memory usage.
///
pub struct ParallelBreadthFirstVisit<
    I,
    E,
    G: RandomAccessGraph,
    T: Borrow<rayon::ThreadPool> = rayon::ThreadPool,
> {
    graph: G,
    granularity: usize,
    visited: AtomicBitVec,
    threads: T,
    _phantom: std::marker::PhantomData<(I, E)>,
}

impl<I, E, G: RandomAccessGraph> ParallelBreadthFirstVisit<I, E, G, rayon::ThreadPool> {
    /// Creates a fair parallel breadth-first visit.
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

    /// Creates a fair parallel top-down visit that uses the specified number of threads.
    ///
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

impl<I, E, G: RandomAccessGraph, T: Borrow<rayon::ThreadPool>>
    ParallelBreadthFirstVisit<I, E, G, T>
{
    /// Creates a fair parallel top-down visit that uses the specified number of threads.
    ///
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

impl<I: QueueItem, E: Send, G: RandomAccessGraph + Sync, T: Borrow<rayon::ThreadPool>>
    ParVisit<Args<I>, E> for ParallelBreadthFirstVisit<I, E, G, T>
{
    fn visit_filtered<C: Fn(&Args<I>) -> Result<(), E> + Sync, F: Fn(&Args<I>) -> bool + Sync>(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        let args = breadth_first::Args::<I> {
            item: I::new(root, root),
            root,
            distance: 0,
            event: breadth_first::Event::Unknown,
        };

        if self.visited.get(root, Ordering::Relaxed) || !filter(&args) {
            return Ok(());
        }

        // We do not provide a capacity in the hope of allocating dynamically
        // space as the frontiers grow.
        let mut curr_frontier = Frontier::with_threads(self.threads.borrow(), None);
        let mut next_frontier = Frontier::with_threads(self.threads.borrow(), None);

        self.threads.borrow().install(|| {
            curr_frontier.push(I::new(root, root));
        });

        self.visited.set(root, true, Ordering::Relaxed);
        let mut distance = 0;

        while !curr_frontier.is_empty() {
            let distance_plus_one = distance + 1;
            self.threads.borrow().install(|| {
                curr_frontier
                    .par_iter()
                    .chunks(self.granularity)
                    .try_for_each(|chunk| {
                        chunk.into_iter().try_for_each(|item| {
                            callback(&breadth_first::Args::<I> {
                                item: *item,
                                root,
                                distance,
                                event: breadth_first::Event::Unknown,
                            })?;
                            let curr = item.curr();
                            self.graph
                                .successors(curr)
                                .into_iter()
                                .try_for_each(|succ| {
                                    if filter(&breadth_first::Args {
                                        item: I::new(succ, curr),
                                        root,
                                        distance: distance_plus_one,
                                        event: breadth_first::Event::Unknown,
                                    }) {
                                        if !self.visited.swap(succ, true, Ordering::Relaxed) {
                                            next_frontier.push(I::new(succ, curr));
                                        } else {
                                            callback(&breadth_first::Args {
                                                item: I::new(succ, curr),
                                                root,
                                                distance: distance_plus_one,
                                                event: breadth_first::Event::Known,
                                            })?;
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
        C: Fn(&Args<I>) -> Result<(), E> + Sync,
        F: Fn(&Args<I>) -> bool + Sync,
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
