use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use rayon::ThreadPool;
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// A simple sequential Breadth First visit on a graph.
///
/// It also implements [`IntoIterator`], so it can be used in `for ... in Visit`.
pub struct ParallelBreadthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
    threads: Option<ThreadPool>,
}

impl<'a, G: RandomAccessGraph> ParallelBreadthFirstVisit<'a, G> {
    /// Constructs a sequential BFV for the specified graph using the provided node factory.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> ParallelBreadthFirstVisit<'a, G> {
        Self::with_start(graph, 0)
    }

    /// Constructs a sequential BFV starting from the node with the specified index in the
    /// provided graph using the provided node factory.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `node_factory`: An immutable reference to the node factory that produces nodes to visit
    /// from their index.
    pub fn with_start(graph: &'a G, start: usize) -> ParallelBreadthFirstVisit<'a, G> {
        ParallelBreadthFirstVisit {
            graph,
            start,
            threads: None,
        }
    }
}

impl<'a, G: RandomAccessGraph> GraphVisit for ParallelBreadthFirstVisit<'a, G> {
    fn visit(self, mut pl: impl ProgressLog) -> Result<BreadthFirstVisitTree> {
        let threads = self.threads.unwrap();

        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a parallel BFV...");

        let mut result = BreadthFirstVisitTreeBuilder::new();

        let visited = AtomicBitVec::new(self.graph.num_nodes());
        let mut next_frontier = Vec::new();

        next_frontier.push(self.start);

        while !next_frontier.is_empty() {
            let mut current_frontier = next_frontier;
            if current_frontier.len() == 1 {
            } else {
            }
            // End visit for current distance
            result.cut();
        }

        pl.done();

        Ok(result.build())
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
        assert!(visit.threads.is_none());

        Ok(())
    }

    #[test]
    fn test_sequential_bfv_new() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let visit = ParallelBreadthFirstVisit::new(&graph);

        assert_eq!(visit.start, 0);
        assert!(visit.threads.is_none());

        Ok(())
    }
}
