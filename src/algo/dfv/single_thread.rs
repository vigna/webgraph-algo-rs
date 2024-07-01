use crate::prelude::*;
use anyhow::Result;
use sux::bits::BitVec;
use webgraph::traits::{RandomAccessGraph, RandomAccessLabeling};

/// Builder for [`SingleThreadedDepthFirstVisit`]
pub struct SingleThreadedDepthFirstVisitBuilder<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
}

impl<'a, G: RandomAccessGraph> SingleThreadedDepthFirstVisitBuilder<'a, G> {
    /// Constructs a new builder with default parameters for specified graph.
    pub fn new(graph: &'a G) -> Self {
        Self { graph, start: 0 }
    }

    /// Sets the starting node for full visits.
    /// It does nothing for single visits using [`DepthFirstGraphVisit::visit_from_node``].
    pub fn with_start(mut self, start: usize) -> Self {
        self.start = start;
        self
    }

    /// Builds the sequential DFV with the builder parameters and consumes the builder.
    pub fn build(self) -> SingleThreadedDepthFirstVisit<'a, G> {
        SingleThreadedDepthFirstVisit {
            graph: self.graph,
            start: self.start,
            stack: Vec::new(),
            visited: BitVec::new(self.graph.num_nodes()),
        }
    }
}

/// A simple sequential Depth First visit on a graph.
pub struct SingleThreadedDepthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
    stack: Vec<(
        <<G as RandomAccessLabeling>::Labels<'a> as IntoIterator>::IntoIter,
        usize,
    )>,
    visited: BitVec,
}

impl<'a, G: RandomAccessGraph> DepthFirstGraphVisit for SingleThreadedDepthFirstVisit<'a, G> {
    fn visit_from_node_filtered<
        C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        visit_root: usize,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Result<()> {
        if self.visited[visit_root] {
            return Ok(());
        }

        let mut current_node = visit_root;
        let mut parent = visit_root;
        let mut iter = self.graph.successors(current_node).into_iter();

        self.visited.set(current_node, true);
        callback(
            current_node,
            parent,
            visit_root,
            0,
            DepthFirstVisitEvent::Discover,
        );

        'recurse: loop {
            let depth = self.stack.len();
            while let Some(succ) = iter.next() {
                // Check if node should be visited
                if filter(succ, current_node, visit_root, depth + 1) {
                    if self.visited[succ] {
                        // Node has already been visited
                        callback(
                            succ,
                            current_node,
                            visit_root,
                            depth + 1,
                            DepthFirstVisitEvent::AlreadyVisited,
                        );
                    } else {
                        // First time seeing node
                        callback(
                            succ,
                            current_node,
                            visit_root,
                            depth + 1,
                            DepthFirstVisitEvent::Discover,
                        );

                        self.visited.set(succ, true);
                        self.stack.push((iter, parent));
                        parent = current_node;
                        current_node = succ;
                        iter = self.graph.successors(current_node).into_iter();

                        continue 'recurse;
                    }
                }
            }

            // Emit node
            callback(
                current_node,
                parent,
                visit_root,
                depth,
                DepthFirstVisitEvent::Emit,
            );

            pl.light_update();

            if let Some((iterator, parent_node)) = self.stack.pop() {
                current_node = parent;
                parent = parent_node;
                iter = iterator;
            } else {
                break;
            }
        }

        Ok(())
    }

    fn visit_graph_filtered<
        C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Result<()> {
        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a sequential DFV...");

        for i in 0..self.graph.num_nodes() {
            let index = (i + self.start) % self.graph.num_nodes();
            self.visit_from_node_filtered(&callback, &filter, index, pl)?;
        }

        pl.done();

        Ok(())
    }
}

impl<'a, G: RandomAccessGraph> ReusableDepthFirstGraphVisit
    for SingleThreadedDepthFirstVisit<'a, G>
{
    #[inline(always)]
    fn reset(&mut self) -> Result<()> {
        self.stack.clear();
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
    fn test_sequential_dfv_with_start() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = SingleThreadedDepthFirstVisitBuilder::new(&graph)
            .with_start(10)
            .build();

        assert_eq!(visit.start, 10);

        Ok(())
    }

    #[test]
    fn test_sequential_dfv_new() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = SingleThreadedDepthFirstVisitBuilder::new(&graph).build();

        assert_eq!(visit.start, 0);

        Ok(())
    }
}
