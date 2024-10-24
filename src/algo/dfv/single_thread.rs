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
    pub fn start(mut self, start: usize) -> Self {
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
    /// Entries on this stack represent the iterator on the successors of a node
    /// and the parent of the node. This approach makes it possible to avoid
    /// storing both the current and the parent node in the stack.
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

        // This variable keeps track of the current node being visited; the
        // parent node is derived at each iteration of the 'recurse loop.
        let mut current_node = visit_root;

        callback(
            visit_root,
            visit_root,
            visit_root,
            0,
            DepthFirstVisitEvent::Discover,
        );

        self.visited.set(current_node, true);
        self.stack
            .push((self.graph.successors(visit_root).into_iter(), visit_root));

        'recurse: loop {
            let depth = self.stack.len();
            let Some((iter, parent)) = self.stack.last_mut() else {
                break;
            };
            let parent_node = *parent;

            for succ in iter.by_ref() {
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
                        // current_node is the parent of succ
                        self.stack
                            .push((self.graph.successors(succ).into_iter(), current_node));
                        // At the next iteration, succ will be the current node
                        current_node = succ;
                        continue 'recurse;
                    }
                }
            }

            // Emit node
            callback(
                current_node,
                parent_node,
                visit_root,
                depth,
                DepthFirstVisitEvent::Emit,
            );

            // We're going up one stack level, so the next current_node
            // is the current parent.
            current_node = parent_node;
            self.stack.pop();

            pl.light_update();
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
    use webgraph::prelude::BvGraph;

    #[test]
    fn test_sequential_dfv_with_start() -> Result<()> {
        let graph = BvGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = SingleThreadedDepthFirstVisitBuilder::new(&graph)
            .start(10)
            .build();

        assert_eq!(visit.start, 10);

        Ok(())
    }

    #[test]
    fn test_sequential_dfv_new() -> Result<()> {
        let graph = BvGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = SingleThreadedDepthFirstVisitBuilder::new(&graph).build();

        assert_eq!(visit.start, 0);

        Ok(())
    }
}
