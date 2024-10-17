use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use std::collections::VecDeque;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// Builder for [`SingleThreadedBreadthFirstVisit`].
#[derive(Clone)]
pub struct SingleThreadedBreadthFirstVisitBuilder<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
}

impl<'a, G: RandomAccessGraph> SingleThreadedBreadthFirstVisitBuilder<'a, G> {
    /// Constructs a new builder with default parameters for specified graph.
    pub fn new(graph: &'a G) -> Self {
        Self { graph, start: 0 }
    }

    /// Sets the starting node for full visits.
    /// It does nothing for single visits using [`BreadthFirstGraphVisit::visit_from_node``].
    pub fn start(mut self, start: usize) -> Self {
        self.start = start;
        self
    }

    /// Builds the sequential BFV with the builder parameters and consumes the builder.
    pub fn build(self) -> SingleThreadedBreadthFirstVisit<'a, G> {
        SingleThreadedBreadthFirstVisit {
            graph: self.graph,
            start: self.start,
            visited: BitVec::new(self.graph.num_nodes()),
            queue: VecDeque::new(),
        }
    }
}

/// A simple sequential Breadth First visit on a graph.
pub struct SingleThreadedBreadthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
    visited: BitVec,
    queue: VecDeque<Option<NonMaxUsize>>,
}

impl<'a, G: RandomAccessGraph> BreadthFirstGraphVisit for SingleThreadedBreadthFirstVisit<'a, G> {
    fn visit_from_node_filtered<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        visit_root: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        if self.visited[visit_root] || !filter(visit_root, visit_root, visit_root, 0) {
            return Ok(());
        }
        self.queue.push_back(Some(
            NonMaxUsize::new(visit_root).expect("node index should never be usize::MAX"),
        ));
        self.queue.push_back(None);
        self.visited.set(visit_root, true);
        callback(visit_root, visit_root, visit_root, 0);

        let mut distance = 1;

        // Visit the connected component
        while let Some(current_node) = self.queue.pop_front() {
            let current_node = current_node.map(|n| n.into());
            match current_node {
                Some(node) => {
                    for succ in self.graph.successors(node) {
                        if !self.visited[succ] && filter(succ, node, visit_root, distance) {
                            callback(succ, node, visit_root, distance);
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

impl<'a, G: RandomAccessGraph> ReusableBreadthFirstGraphVisit
    for SingleThreadedBreadthFirstVisit<'a, G>
{
    #[inline(always)]
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
    use webgraph::prelude::BvGraph;

    #[test]
    fn test_sequential_bfv_with_start() -> Result<()> {
        let graph = BvGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = SingleThreadedBreadthFirstVisitBuilder::new(&graph)
            .start(10)
            .build();

        assert_eq!(visit.start, 10);

        Ok(())
    }

    #[test]
    fn test_sequential_bfv_new() -> Result<()> {
        let graph = BvGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = SingleThreadedBreadthFirstVisitBuilder::new(&graph).build();

        assert_eq!(visit.start, 0);

        Ok(())
    }
}
