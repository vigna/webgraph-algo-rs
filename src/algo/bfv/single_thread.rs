use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use std::collections::VecDeque;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// A simple sequential Breadth First visit on a graph.
pub struct SingleThreadedBreadthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
    visited: BitVec,
    queue: VecDeque<Option<NonMaxUsize>>,
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
    fn visit_from_node_filtered<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        node_index: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        if self.visited[node_index] || !filter(node_index, node_index, node_index, 0) {
            return Ok(());
        }
        self.queue.push_back(Some(
            NonMaxUsize::new(node_index).expect("node index should never be usize::MAX"),
        ));
        self.queue.push_back(None);
        self.visited.set(node_index, true);
        callback(node_index, node_index, node_index, 0);

        let mut distance = 1;

        // Visit the connected component
        while let Some(current_node) = self.queue.pop_front() {
            let current_node = current_node.map(|n| n.into());
            match current_node {
                Some(node) => {
                    for succ in self.graph.successors(node) {
                        if !self.visited[succ] && filter(succ, node, node_index, distance) {
                            callback(succ, node, node_index, distance);
                            self.visited.set(succ, true);
                            self.queue.push_back(Some(
                                NonMaxUsize::new(succ)
                                    .expect("node index should never be usize::MAX"),
                            ))
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

    fn visit_graph_filtered<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a sequential BFV...");

        for i in 0..self.graph.num_nodes() {
            let index = (i + self.start) % self.graph.num_nodes();
            self.visit_from_node_filtered(&callback, &filter, index, pl)?;
        }

        pl.done();

        Ok(())
    }
}

impl<'a, G: RandomAccessGraph> ReusableGraphVisit for SingleThreadedBreadthFirstVisit<'a, G> {
    fn reset(&mut self) -> Result<()> {
        self.queue.clear();
        self.visited.fill(false);
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
