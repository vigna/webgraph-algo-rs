use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::iter::IntoParallelIterator;
use rayon::prelude::*;
use std::sync::atomic::Ordering;
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// A simple parallel Breadth First visit on a graph.
pub struct ParallelBreadthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
    granularity: usize,
    visited: AtomicBitVec,
}

impl<'a, G: RandomAccessGraph> ParallelBreadthFirstVisit<'a, G> {
    /// Constructs a parallel BFV for the specified graph.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> ParallelBreadthFirstVisit<'a, G> {
        Self::with_start(graph, 0)
    }

    /// Constructs a parallel BFV starting from the node with the specified index in the
    /// provided graph.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `start`: The starting node.
    pub fn with_start(graph: &'a G, start: usize) -> ParallelBreadthFirstVisit<'a, G> {
        Self::with_parameters(graph, start, 1)
    }

    /// Constructs a parallel BFV using the specified parallelism split granularity with
    /// respect to the number of threads in the provided graph.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `granularity`: How many fragments per thread to generate.
    pub fn with_granularity(graph: &'a G, granularity: usize) -> ParallelBreadthFirstVisit<'a, G> {
        Self::with_parameters(graph, 0, granularity)
    }

    /// Constructs a parallel BFV starting from the node with the specified index and using the
    /// specified parallelism split granularity with respect to the number of threads in the provided graph.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `start`: The starting node.
    /// - `granularity`: How many fragments per thread to generate.
    pub fn with_parameters(
        graph: &'a G,
        start: usize,
        granularity: usize,
    ) -> ParallelBreadthFirstVisit<'a, G> {
        ParallelBreadthFirstVisit {
            graph,
            start,
            granularity,
            visited: AtomicBitVec::new(graph.num_nodes()),
        }
    }
}

impl<'a, G: RandomAccessGraph + Sync> GraphVisit for ParallelBreadthFirstVisit<'a, G> {
    fn visit_node(&mut self, node_index: usize, pl: &mut impl ProgressLog) -> Result<()> {
        if self.visited.get(node_index, Ordering::Relaxed) {
            return Ok(());
        }

        let num_threads = rayon::current_num_threads();
        let scaled_threads = num_threads * self.granularity;
        let mut next_frontier = Frontier::new();

        next_frontier.push(self.start);
        self.visited.set(self.start, true, Ordering::Relaxed);

        // Visit the connected component
        while !next_frontier.is_empty() {
            let current_frontier = next_frontier;
            let current_len = current_frontier.len();
            let chunk_size = std::cmp::max(current_len / scaled_threads, 1);
            next_frontier = Frontier::new();
            current_frontier
                .par_iter()
                .chunks(chunk_size)
                .for_each(|chunk| {
                    chunk.into_par_iter().for_each(|&node_index| {
                        self.graph
                            .successors(node_index)
                            .into_iter()
                            .for_each(|succ| {
                                if !self.visited.swap(succ, true, Ordering::Relaxed) {
                                    next_frontier.push(succ);
                                }
                            })
                    })
                });
            pl.update_with_count(current_len);
        }

        Ok(())
    }

    fn visit(mut self, mut pl: impl ProgressLog) -> Result<()> {
        let num_threads = rayon::current_num_threads();

        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a parallel BFV...");
        pl.info(format_args!(
            "Using {} threads with {} fragments per thread...",
            num_threads, self.granularity
        ));

        for i in 0..self.graph.num_nodes() {
            let index = (i + self.start) % self.graph.num_nodes();
            self.visit_node(index, &mut pl)?;
        }

        pl.done();

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Context;
    use webgraph::graphs::BVGraph;

    #[test]
    fn test_sequential_bfv_with_parameters() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisit::with_parameters(&graph, 10, 2);

        assert_eq!(visit.start, 10);
        assert_eq!(visit.granularity, 2);

        Ok(())
    }

    #[test]
    fn test_sequential_bfv_with_start() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisit::with_start(&graph, 10);

        assert_eq!(visit.start, 10);
        assert_eq!(visit.granularity, 1);

        Ok(())
    }

    #[test]
    fn test_sequential_bfv_with_granularity() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisit::with_granularity(&graph, 10);

        assert_eq!(visit.start, 0);
        assert_eq!(visit.granularity, 10);

        Ok(())
    }

    #[test]
    fn test_sequential_bfv_new() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisit::new(&graph);

        assert_eq!(visit.start, 0);
        assert_eq!(visit.granularity, 1);

        Ok(())
    }
}
