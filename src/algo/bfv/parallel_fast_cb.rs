use crate::{prelude::*, utils::Threads};
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::{borrow::Borrow, sync::atomic::Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// Builder for [`ParallelBreadthFirstVisitFastCB`].
#[derive(Clone)]
pub struct ParallelBreadthFirstVisitFastCBBuilder<'a, G: RandomAccessGraph, T = Threads> {
    graph: &'a G,
    granularity: usize,
    threads: T,
}

impl<'a, G: RandomAccessGraph> ParallelBreadthFirstVisitFastCBBuilder<'a, G, Threads> {
    /// Constructs a new builder with default parameters for specified graph.
    pub fn new(graph: &'a G) -> Self {
        Self {
            graph,
            granularity: 1,
            threads: Threads::Default,
        }
    }
}

impl<'a, G: RandomAccessGraph, T> ParallelBreadthFirstVisitFastCBBuilder<'a, G, T> {
    /// Sets the number of nodes in each chunk of the frontier to explore.
    ///
    /// High granularity reduces overhead, but may lead to decreased performance
    /// on graphs with skewed outdegrees.
    pub fn granularity(mut self, granularity: usize) -> Self {
        self.granularity = granularity;
        self
    }

    /// Sets the visit to use the default threadpool.
    pub fn default_threadpool(self) -> ParallelBreadthFirstVisitFastCBBuilder<'a, G> {
        ParallelBreadthFirstVisitFastCBBuilder {
            graph: self.graph,
            granularity: self.granularity,
            threads: Threads::Default,
        }
    }

    /// Sets the visit to use a [`rayon::ThreadPool`] with the specified number of threads.
    pub fn num_threads(self, num_threads: usize) -> ParallelBreadthFirstVisitFastCBBuilder<'a, G> {
        ParallelBreadthFirstVisitFastCBBuilder {
            graph: self.graph,
            granularity: self.granularity,
            threads: Threads::NumThreads(num_threads),
        }
    }

    /// Sets the visit to use the custop [`rayon::ThreadPool`].
    pub fn threadpool<T2: Borrow<rayon::ThreadPool>>(
        self,
        threadpool: T2,
    ) -> ParallelBreadthFirstVisitFastCBBuilder<'a, G, T2> {
        ParallelBreadthFirstVisitFastCBBuilder {
            graph: self.graph,
            granularity: self.granularity,
            threads: threadpool,
        }
    }
}

impl<'a, G: RandomAccessGraph> ParallelBreadthFirstVisitFastCBBuilder<'a, G, Threads> {
    /// Builds the parallel BFV with the builder parameters and consumes the builder.
    pub fn build(self) -> ParallelBreadthFirstVisitFastCB<'a, G> {
        let builder = ParallelBreadthFirstVisitFastCBBuilder {
            graph: self.graph,
            granularity: self.granularity,
            threads: self.threads.build(),
        };
        builder.build()
    }
}

impl<'a, G: RandomAccessGraph, T: Borrow<rayon::ThreadPool>>
    ParallelBreadthFirstVisitFastCBBuilder<'a, G, T>
{
    /// Builds the parallel BFV with the builder parameters and consumes the builder.
    pub fn build(self) -> ParallelBreadthFirstVisitFastCB<'a, G, T> {
        ParallelBreadthFirstVisitFastCB {
            graph: self.graph,
            granularity: self.granularity,
            visited: AtomicBitVec::new(self.graph.num_nodes()),
            threads: self.threads,
        }
    }
}

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
