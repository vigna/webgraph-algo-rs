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
    visited: BitVec,
    queue: VecDeque<Option<usize>>,
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
        SingleThreadedBreadthFirstVisit {
            graph,
            start,
            visited: BitVec::new(graph.num_nodes()),
            queue: VecDeque::new(),
        }
    }
}

impl<'a, G: RandomAccessGraph> GraphVisit for SingleThreadedBreadthFirstVisit<'a, G> {
    fn visit_component<F: Fn(usize, usize) + Sync>(
        &mut self,
        callback: F,
        node_index: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        if self.visited[node_index] {
            return Ok(());
        }
        self.queue.push_back(Some(node_index));
        self.queue.push_back(None);
        self.visited.set(node_index, true);

        let mut distance = 0;

        // Visit the connected component
        while !self.queue.is_empty() {
            let current_node = self.queue.pop_front().unwrap();
            match current_node {
                Some(node) => {
                    callback(node, distance);
                    for succ in self.graph.successors(node) {
                        if !self.visited[succ] {
                            self.visited.set(succ, true);
                            self.queue.push_back(Some(succ))
                        }
                    }
                    pl.light_update();
                }
                None => {
                    if !self.queue.is_empty() {
                        distance += 1;
                        self.queue.push_back(None);
                    }
                }
            }
        }

        Ok(())
    }

    fn visit<F: Fn(usize, usize) + Sync>(
        mut self,
        callback: F,
        mut pl: impl ProgressLog,
    ) -> Result<()> {
        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a sequential BFV...");

        for i in 0..self.graph.num_nodes() {
            let index = (i + self.start) % self.graph.num_nodes();
            self.visit_component(&callback, index, &mut pl)?;
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
