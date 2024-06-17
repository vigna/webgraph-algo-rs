use crate::prelude::*;
use webgraph::traits::RandomAccessGraph;

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
        }
    }
}

/// A simple sequential Depth First visit on a graph.
pub struct SingleThreadedDepthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    start: usize,
}

impl<'a, G: RandomAccessGraph> DepthFirstGraphVisit for SingleThreadedDepthFirstVisit<'a, G> {
    fn visit_from_node_filtered<
        C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        node_index: usize,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> anyhow::Result<()> {
        todo!()
    }

    fn visit_graph_filtered<
        C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> anyhow::Result<()> {
        todo!()
    }
}
