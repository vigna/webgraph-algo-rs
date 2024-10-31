//! Module containing all algorithms implementations for WebGraph

pub mod visits;

pub mod diameter;

mod strongly_connected_components;

pub mod hyperball;

/// Algorithms used to compute and work with strongly connected
/// components in a graph.
pub mod scc {
    use super::strongly_connected_components;
    pub use strongly_connected_components::*;
}

/// Traits used to interact with the implemented algorithms.
pub mod traits {
    use super::*;

    pub use strongly_connected_components::traits::*;
    pub use visits::{ParVisit, SeqVisit};
}
