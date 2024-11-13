//! An implementation of the [ExactSumSweep algorithm](DirExactSumSweep).
//!
//! The algorithm has been described by Michele Borassi, Pierluigi Crescenzi,
//! Michel Habib, Walter A. Kosters, Andrea Marino, and Frank W. Takes in “[Fast
//! diameter and radius BFS-based computation in (weakly connected) real-world
//! graphs–With an application to the six degrees of separation
//! games](https://www.sciencedirect.com/science/article/pii/S0304397515001644)”,
//! *Theoretical Computer Science*, 586:59–80, Elsevier, 2015. [DOI
//! 10.1016/j.tcs.2015.02.033](https://doi.org/10.1016/j.tcs.2015.02.033).

/// The possible outputs of [ExactSumSweep](DirExactSumSweep)
///
/// Note that the items have a slightly different meaning for the
/// [`directed`](`DirExactSumSweep`) and the [`undirected`](`UndirExactSumSweep`)
/// case.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum OutputLevel {
    /// Compute all the eccentricities of the graph.
    ///
    /// This variant is equivalent to [`AllForward`](`Self::AllForward`) in the undirected case.
    All,
    /// Compute all the forward eccentricities of the graph.
    AllForward,
    /// Computes both the diameter and the radius of the graph.
    RadiusDiameter,
    /// Computes the diameter of the graph.
    Diameter,
    /// Computers the radius of the graph.
    Radius,
}

mod scc_graph;

mod exact_sum_sweep;
pub use exact_sum_sweep::*;

mod undirected;
pub use undirected::*;
