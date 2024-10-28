pub mod visits;

pub mod diameter;

mod strongly_connected_components;

pub mod hyperball;

/// Strongly connected components
pub mod scc {
    use super::strongly_connected_components;
    pub use strongly_connected_components::*;
}

pub mod traits {
    use super::strongly_connected_components;
    pub use super::visits::bfv;
    pub use super::visits::dfv;

    pub use strongly_connected_components::traits::*;
}
