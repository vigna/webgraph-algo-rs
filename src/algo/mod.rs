//! Module containing all algorithms implementations for WebGraph

pub mod visits;

pub mod exact_sum_sweep;

pub mod sccs;

mod acyclicity;
pub use acyclicity::acyclicity;
mod top_sort;
pub use top_sort::top_sort;

pub mod hyperball;

/// Traits used to interact with the implemented algorithms.
pub mod traits {
    use super::*;

    pub use acyclicity::Acyclicity;
    pub use sccs::StronglyConnectedComponents;
    pub use visits::{Parallel, Sequential};
}
