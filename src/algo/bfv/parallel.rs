use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::iter::IntoParallelIterator;
use std::sync::atomic::Ordering;
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// A simple sequential Breadth First visit on a graph.
///
/// It also implements [`IntoIterator`], so it can be used in `for ... in Visit`.
pub struct ParallelBreadthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
}

impl<'a, G: RandomAccessGraph> ParallelBreadthFirstVisit<'a, G> {
    /// Constructs a sequential BFV for the specified graph.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> ParallelBreadthFirstVisit<'a, G> {
        Self::with_start(graph, 0)
    }

    /// Constructs a sequential BFV starting from the node with the specified index in the
    /// provided graph.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `start`: The starting node.
    pub fn with_start(graph: &'a G, start: usize) -> ParallelBreadthFirstVisit<'a, G> {
        ParallelBreadthFirstVisit { graph, start }
    }
}

impl<'a, G: RandomAccessGraph + Sync> GraphVisit for ParallelBreadthFirstVisit<'a, G> {
    fn visit(self, mut pl: impl ProgressLog) -> Result<()> {
        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a parallel BFV...");

        let visited = AtomicBitVec::new(self.graph.num_nodes());
        let mut next_frontier = Frontier::new();
        let mut remaining_nodes = self.graph.num_nodes();

        next_frontier.push(self.start);
        visited.set(self.start, true, Ordering::Relaxed);

        // Visit the connected component
        while !next_frontier.is_empty() {
            let current_frontier = next_frontier;
            let current_len = current_frontier.len();
            next_frontier = Frontier::new();
            current_frontier.par_iter().for_each(|&element| {
                self.graph.successors(element).into_iter().for_each(|succ| {
                    if !visited.swap(succ, true, Ordering::Relaxed) {
                        next_frontier.push(succ);
                    }
                })
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
    fn test_sequential_bfv_with_start() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisit::with_start(&graph, 10);

        assert_eq!(visit.start, 10);

        Ok(())
    }

    #[test]
    fn test_sequential_bfv_new() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisit::new(&graph);

        assert_eq!(visit.start, 0);

        Ok(())
    }
}
