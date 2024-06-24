use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::sync::atomic::Ordering;
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// Builder for [`ParallelBreadthFirstVisitLowMem`].
#[derive(Clone)]
pub struct ParallelBreadthFirstVisitLowMemBuilder<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
    granularity: usize,
}

impl<'a, G: RandomAccessGraph> ParallelBreadthFirstVisitLowMemBuilder<'a, G> {
    /// Constructs a new builder with default parameters for specified graph.
    pub fn new(graph: &'a G) -> Self {
        Self {
            graph,
            start: 0,
            granularity: 1,
        }
    }

    /// Sets the starting node for full visits.
    /// It does nothing for single visits using [`BreadthFirstGraphVisit::visit_from_node`].
    pub fn with_start(mut self, start: usize) -> Self {
        self.start = start;
        self
    }

    /// Sets the number of nodes in each chunk of the frontier to explore.
    ///
    /// High granularity reduces overhead, but may lead to decreased performance
    /// on graphs with skewed outdegrees.
    pub fn with_granularity(mut self, granularity: usize) -> Self {
        self.granularity = granularity;
        self
    }

    /// Builds the sequential BFV with the builder parameters and consumes the builder.
    pub fn build(self) -> ParallelBreadthFirstVisitLowMem<'a, G> {
        ParallelBreadthFirstVisitLowMem {
            graph: self.graph,
            start: self.start,
            granularity: self.granularity,
            visited: AtomicBitVec::new(self.graph.num_nodes()),
        }
    }
}

/// A simple parallel Breadth First visit on a graph with low memory consumption but with a smaller
/// frontier.
pub struct ParallelBreadthFirstVisitLowMem<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
    granularity: usize,
    visited: AtomicBitVec,
}

impl<'a, G: RandomAccessGraph + Sync> BreadthFirstGraphVisit
    for ParallelBreadthFirstVisitLowMem<'a, G>
{
    fn visit_from_node_filtered<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        root: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        if self.visited.get(root, Ordering::Relaxed) || !filter(root, root, root, 0) {
            return Ok(());
        }

        let mut next_frontier = Frontier::new();

        next_frontier.push(root);
        self.visited.set(root, true, Ordering::Relaxed);
        callback(root, root, root, 0);

        let mut distance = 1;

        // Visit the connected component
        while !next_frontier.is_empty() {
            let current_frontier = next_frontier;
            let current_len = current_frontier.len();
            next_frontier = Frontier::new();
            current_frontier
                .par_iter()
                .chunks(self.granularity)
                .for_each(|chunk| {
                    chunk.into_iter().for_each(|&node| {
                        self.graph.successors(node).into_iter().for_each(|succ| {
                            if filter(succ, node, root, distance)
                                && !self.visited.swap(succ, true, Ordering::Relaxed)
                            {
                                callback(succ, node, root, distance);
                                next_frontier.push(succ);
                            }
                        })
                    })
                });
            pl.update_with_count(current_len);
            distance += 1;
        }

        Ok(())
    }

    fn visit_graph_filtered<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        let num_threads = rayon::current_num_threads();

        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a parallel BFV...");
        pl.info(format_args!(
            "Using {} threads with block size {}...",
            num_threads, self.granularity
        ));

        for i in 0..self.graph.num_nodes() {
            let index = (i + self.start) % self.graph.num_nodes();
            self.visit_from_node_filtered(&callback, &filter, index, pl)?;
        }

        pl.done();

        Ok(())
    }
}

impl<'a, G: RandomAccessGraph + Sync> ReusableBreadthFirstGraphVisit
    for ParallelBreadthFirstVisitLowMem<'a, G>
{
    fn reset(&mut self) -> Result<()> {
        self.visited.fill(false, Ordering::Relaxed);
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Context;
    use webgraph::graphs::BVGraph;

    #[test]
    fn test_parallel_low_mem_bfv_with_parameters() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisitLowMemBuilder::new(&graph)
            .with_start(10)
            .with_granularity(2)
            .build();

        assert_eq!(visit.start, 10);
        assert_eq!(visit.granularity, 2);

        Ok(())
    }

    #[test]
    fn test_parallel_bfv_low_mem_with_start() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisitLowMemBuilder::new(&graph)
            .with_start(10)
            .build();

        assert_eq!(visit.start, 10);
        assert_eq!(visit.granularity, 1);

        Ok(())
    }

    #[test]
    fn test_parallel_bfv_low_mem_with_granularity() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisitLowMemBuilder::new(&graph)
            .with_granularity(10)
            .build();

        assert_eq!(visit.start, 0);
        assert_eq!(visit.granularity, 10);

        Ok(())
    }

    #[test]
    fn test_parallel_low_mem_bfv_new() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisitLowMemBuilder::new(&graph).build();

        assert_eq!(visit.start, 0);
        assert_eq!(visit.granularity, 1);

        Ok(())
    }
}
