//! Module containing all algorithms implementations for WebGraph

pub mod visits;

pub mod exact_sum_sweep;

mod sccs;

pub mod acyclicity;
pub mod top_sort;

pub mod hyperball;

/// Algorithms used to compute and work with strongly connected
/// components in a graph.
pub mod scc {
    use super::sccs;
    pub use sccs::*;
}

/// Traits used to interact with the implemented algorithms.
pub mod traits {
    use super::*;

    pub use sccs::traits::*;
    pub use visits::{Parallel, Sequential};
}
