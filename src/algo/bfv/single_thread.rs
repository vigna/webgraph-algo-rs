use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use std::collections::VecDeque;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// A simple sequential Breadth First visit on a graph.
pub struct SingleThreadedBreadthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
}

impl<'a, G: RandomAccessGraph> SingleThreadedBreadthFirstVisit<'a, G> {
    /// Constructs a sequential BFV for the specified graph.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> SingleThreadedBreadthFirstVisit<'a, G> {
        Self::with_start(graph, 0)
    }

    /// Constructs a sequential BFV starting from the node with the specified index in the
    /// provided graph.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `node_factory`: An immutable reference to the node factory that produces nodes to visit
    /// from their index.
    pub fn with_start(graph: &'a G, start: usize) -> SingleThreadedBreadthFirstVisit<'a, G> {
        SingleThreadedBreadthFirstVisit { graph, start }
    }
}

impl<'a, G: RandomAccessGraph> GraphVisit for SingleThreadedBreadthFirstVisit<'a, G> {
    fn visit(self, mut pl: impl ProgressLog) -> Result<()> {
        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a sequential BFV...");

        let mut visited = BitVec::new(self.graph.num_nodes());
        let mut queue = VecDeque::new();

        visited.set(self.start, true);
        queue.push_back(self.start);

        // Visit the connected component
        while !queue.is_empty() {
            let current_node = queue.pop_front().unwrap();
            for succ in self.graph.successors(current_node) {
                if !visited[succ] {
                    visited.set(succ, true);
                    queue.push_back(succ);
                }
            }
            pl.light_update();
        }

        // Visit the remaining nodes
        for index in 0..self.graph.num_nodes() {
            if !visited[index] {
                pl.light_update();
            }
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
    fn test_sequential_bfv_with_start() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = SingleThreadedBreadthFirstVisit::with_start(&graph, 10);

        assert_eq!(visit.start, 10);

        Ok(())
    }

    #[test]
    fn test_sequential_bfv_new() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = SingleThreadedBreadthFirstVisit::new(&graph);

        assert_eq!(visit.start, 0);

        Ok(())
    }
}
