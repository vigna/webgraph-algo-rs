use crate::algo::bfv::{parallel::*, parallel_fast_cb::*, single_thread::*};
use webgraph::traits::RandomAccessGraph;

/// Utility struct to requests builders for Breadth-First visits of graphs.
pub struct BFVBuilder;

impl BFVBuilder {
    /// Creates a new builder for a sequential visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new_sequential<G: RandomAccessGraph>(
        graph: &G,
    ) -> SingleThreadedBreadthFirstVisitBuilder<G> {
        SingleThreadedBreadthFirstVisitBuilder::new(graph)
    }

    /// Creates a new builder for a parallel top-down visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new_parallel<G: RandomAccessGraph>(graph: &G) -> ParallelBreadthFirstVisitBuilder<G> {
        ParallelBreadthFirstVisitBuilder::new(graph)
    }

    /// Creates a new builder for a parallel top-down visit that uses less memory
    /// but is less efficient with long callbacks.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new_parallel_fast_callback<G: RandomAccessGraph>(
        graph: &G,
    ) -> ParallelBreadthFirstVisitFastCBBuilder<G> {
        ParallelBreadthFirstVisitFastCBBuilder::new(graph)
    }
}
