use crate::algo::bfv::{parallel::*, parallel_low_mem::*, single_thread::*};
use webgraph::traits::RandomAccessGraph;

/// Utility struct to requests builders for Breadth-First visits of graphs.
pub struct BFV;

impl BFV {
    /// Creates a new builder for a sequential visit.
    ///
    /// # Arguments
    /// - `graph`: an immutable reference to the graph to visit.
    pub fn new_sequential<G: RandomAccessGraph>(
        graph: &G,
    ) -> SingleThreadedBreadthFirstVisitBuilder<G> {
        SingleThreadedBreadthFirstVisitBuilder::new(graph)
    }

    /// Creates a new builder for a parallel top-down visit.
    ///
    /// # Arguments
    /// - `graph`: an immutable reference to the graph to visit.
    pub fn new_parallel<G: RandomAccessGraph>(graph: &G) -> ParallelBreadthFirstVisitBuilder<G> {
        ParallelBreadthFirstVisitBuilder::new(graph)
    }

    /// Creates a new builder for a parallel top-down visit that uses less memory
    /// but is less efficient on graphs with skewed outdegrees.
    ///
    /// # Arguments
    /// - `graph`: an immutable reference to the graph to visit.
    pub fn new_parallel_low_mem<G: RandomAccessGraph>(
        graph: &G,
    ) -> ParallelBreadthFirstVisitLowMemBuilder<G> {
        ParallelBreadthFirstVisitLowMemBuilder::new(graph)
    }
}
