use crate::algo::visits::{breadth_first, ParVisit};
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::{borrow::Borrow, sync::atomic::Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// A parallel visit where the
/// callback is called during successor enumeration, allowing to store only the nodes without their parents.
/// This leads to slowdowns and less parallelization in the case where the callback is not trascurable relative
/// to the visit logic but to performance improvements in case it is.
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
    /// Creates parallel top-down visit that uses less memory
    /// but is less efficient with long callbacks.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
    pub fn new(graph: G, granularity: usize) -> Self {
        Self::with_num_threads(graph, granularity, 0)
    }

    /// Creates a parallel top-down visit faster for quick callbacks but slower and less
    /// for longer ones that uses the specified number of threads.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
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
    /// Creates a parallel top-down visit faster for quick callbacks but slower and less
    /// for longer ones that uses the specified threadpool.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
    /// * `threads`: the threadpool to use.
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

impl<E: Send, G: RandomAccessGraph + Sync, T: Borrow<rayon::ThreadPool>> ParVisit<breadth_first::Args, E>
    for ParallelBreadthFirstVisitFastCB<E, G, T>
{
    fn visit_from_node_filtered<
        C: Fn(&breadth_first::Args) -> Result<(), E> + Sync,
        F: Fn(&breadth_first::Args) -> bool + Sync,
    >(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        let args = breadth_first::Args {
            node: root,
            parent: root,
            root,
            distance: 0,
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
                                    let args = breadth_first::Args {
                                        node: succ,
                                        parent: node,
                                        root,
                                        distance,
                                    };
                                    if filter(&args)
                                        && !self.visited.swap(succ, true, Ordering::Relaxed)
                                    {
                                        callback(&args)?;
                                        next_frontier.push(succ);
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

    fn visit<C: Fn(&breadth_first::Args) -> Result<(), E> + Sync, F: Fn(&breadth_first::Args) -> bool + Sync>(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Result<(), E> {
        for node in 0..self.graph.num_nodes() {
            self.visit_from_node_filtered(node, &callback, &filter, pl)?;
        }

        Ok(())
    }

    fn reset(&mut self) {
        self.visited.fill(false, Ordering::Relaxed);
    }
}
