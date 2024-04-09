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
        }
    }
}

impl<'a, G: RandomAccessGraph + Sync> GraphVisit for ParallelBreadthFirstVisit<'a, G> {
    fn visit(self, mut pl: impl ProgressLog) -> Result<()> {
        let visited = AtomicBitVec::new(self.graph.num_nodes());
        let num_threads = rayon::current_num_threads();
        let scaled_threads = num_threads * self.granularity;
        let mut next_frontier = Frontier::new();
        let mut remaining_nodes = self.graph.num_nodes();

        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a parallel BFV...");
        pl.info(format_args!(
            "Using {} threads with {} fragments per thread...",
            num_threads, self.granularity
        ));

        next_frontier.push(self.start);
        visited.set(self.start, true, Ordering::Relaxed);

        // Visit the connected component
        while !next_frontier.is_empty() {
            let current_frontier: Vec<Vec<_>> = next_frontier.into();
            let current_len = current_frontier.len();
            next_frontier = Frontier::new();
            current_frontier.par_iter().for_each(|v| {
                let chunk_size = std::cmp::max(v.len() / scaled_threads, 1);
                v.par_chunks(chunk_size).for_each(|chunk| {
                    chunk.par_iter().for_each(|&node_index| {
                        self.graph
                            .successors(node_index)
                            .into_iter()
                            .for_each(|succ| {
                                if !visited.swap(succ, true, Ordering::Relaxed) {
                                    next_frontier.push(succ);
                                }
                            })
                    })
                });
            });
            remaining_nodes -= current_len;
            pl.update_with_count(current_len);
        }

        // Visit the remaining nodes
        (0..self.graph.num_nodes())
            .into_par_iter()
            .filter(|&element| !visited.get(element, Ordering::Relaxed))
            .for_each(|_| {});

        pl.update_with_count(remaining_nodes);

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
