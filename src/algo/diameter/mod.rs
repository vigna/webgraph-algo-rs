//! An implementation of the [ExactSumSweep algorithm](dir_sum_sweep).
//!
//! The algorithm has been described by Michele Borassi, Pierluigi Crescenzi,
//! Michel Habib, Walter A. Kosters, Andrea Marino, and Frank W. Takes in “[Fast
//! diameter and radius BFS-based computation in (weakly connected) real-world
//! graphs–With an application to the six degrees of separation
//! games](https://www.sciencedirect.com/science/article/pii/S0304397515001644)”,
//! *Theoretical Computer Science*, 586:59–80, Elsevier, 2015. [DOI
//! 10.1016/j.tcs.2015.02.033](https://doi.org/10.1016/j.tcs.2015.02.033).

/// The possible outputs of [ExactSumSweep](dir_sum_sweep)
///
/// Note that the items have a slightly different meaning for the
/// [`directed`](`dir_sum_sweep`) and the [`undirected`](`undir_sum_sweep`)
/// case.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum OutputLevel {
    /// Compute all the eccentricities of the graph.
    All,
    /// Compute all the forward eccentricities of the graph.
    ///
    /// This variant is equivalent to [`All`](`Self::All`) in the undirected case.
    AllForward,
    /// Computes both the diameter and the radius of the graph.
    RadiusDiameter,
    /// Computes the diameter of the graph.
    Diameter,
    /// Computers the radius of the graph.
    Radius,
}

mod scc_graph;

mod dir_sum_sweep;
pub use dir_sum_sweep::*;

mod undir_sum_sweep;
pub use undir_sum_sweep::*;
