use crate::algo::dfv::single_thread::*;
use webgraph::traits::RandomAccessGraph;

/// Utility struct to requests builders for Depth-First visits of graphs.
pub struct DFVBuilder;

impl DFVBuilder {
    /// Creates a new builder for a sequential visit.
    ///
    /// # Arguments
    /// - `graph`: an immutable reference to the graph to visit.
    pub fn new_sequential<G: RandomAccessGraph>(
        graph: &G,
    ) -> SingleThreadedDepthFirstVisitBuilder<G> {
        SingleThreadedDepthFirstVisitBuilder::new(graph)
    }
}
