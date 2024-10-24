use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::{borrow::Borrow, sync::atomic::Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// A simple parallel Breadth First visit on a graph with low memory consumption but with a smaller
/// frontier.
pub struct ParallelBreadthFirstVisitFastCB<
    'a,
    G: RandomAccessGraph,
    T: Borrow<rayon::ThreadPool> = rayon::ThreadPool,
> {
    graph: &'a G,
    granularity: usize,
    visited: AtomicBitVec,
    threads: T,
}

impl<'a, G: RandomAccessGraph> ParallelBreadthFirstVisitFastCB<'a, G, rayon::ThreadPool> {
    /// Creates parallel top-down visit that uses less memory
    /// but is less efficient with long callbacks.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
    pub fn new(graph: &'a G, granularity: usize) -> Self {
        Self::with_num_threads(graph, granularity, 0)
    }

    /// Creates a parallel top-down visit that uses the specified number of threads, less memory
    /// but is less efficient with long callbacks.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
    /// * `num_threads`: the number of threads to use.
    pub fn with_num_threads(graph: &'a G, granularity: usize, num_threads: usize) -> Self {
        let threads = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .unwrap_or_else(|_| panic!("Could not build threadpool with {} threads", num_threads));
        Self::with_threads(graph, granularity, threads)
    }
}

impl<'a, G: RandomAccessGraph, T: Borrow<rayon::ThreadPool>>
    ParallelBreadthFirstVisitFastCB<'a, G, T>
{
    /// Creates a parallel top-down visit that uses the specified threadpool, less memory
    /// but is less efficient with long callbacks.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
    /// * `threads`: the threadpool to use.
    pub fn with_threads(graph: &'a G, granularity: usize, threads: T) -> Self {
        Self {
            graph,
            granularity,
            visited: AtomicBitVec::new(graph.num_nodes()),
            threads,
        }
    }
}

impl<'a, G: RandomAccessGraph + Sync, T: Borrow<rayon::ThreadPool>> BreadthFirstGraphVisit
    for ParallelBreadthFirstVisitFastCB<'a, G, T>
{
    fn visit_from_node_filtered<C: Fn(BFVArgs) + Sync, F: Fn(BFVArgs) -> bool + Sync>(
        &mut self,
        callback: C,
        filter: F,
        visit_root: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        let args = BFVArgs {
            node_index: visit_root,
            parent: visit_root,
            root: visit_root,
            distance_from_root: 0,
        };
        if self.visited.get(visit_root, Ordering::Relaxed) || !filter(args) {
            return Ok(());
        }

        // We do not provide a capacity in the hope of allocating dyinamically
        // space as the frontiers grow.
        let mut curr_frontier = Frontier::with_threads(self.threads.borrow(), None);
        let mut next_frontier = Frontier::with_threads(self.threads.borrow(), None);

        self.threads
            .borrow()
            .install(|| curr_frontier.push(visit_root));

        self.visited.set(visit_root, true, Ordering::Relaxed);
        callback(args);

        let mut distance = 1;

        // Visit the connected component
        while !curr_frontier.is_empty() {
            self.threads.borrow().install(|| {
                curr_frontier
                    .par_iter()
                    .chunks(self.granularity)
                    .for_each(|chunk| {
                        chunk.into_iter().for_each(|&node| {
                            self.graph.successors(node).into_iter().for_each(|succ| {
                                let args = BFVArgs {
                                    node_index: succ,
                                    parent: node,
                                    root: visit_root,
                                    distance_from_root: distance,
                                };
                                if filter(args) && !self.visited.swap(succ, true, Ordering::Relaxed)
                                {
                                    callback(args);
                                    next_frontier.push(succ);
                                }
                            })
                        })
                    });
            });
            pl.update_with_count(curr_frontier.len());
            distance += 1;
            // Swap the frontiers
            std::mem::swap(&mut curr_frontier, &mut next_frontier);
            // Clear the frontier we will fill in the next iteration
            next_frontier.clear();
        }

        Ok(())
    }

    #[inline(always)]
    fn reset(&mut self) -> Result<()> {
        self.visited.fill(false, Ordering::Relaxed);
        Ok(())
    }
}
