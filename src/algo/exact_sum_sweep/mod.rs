//! An implementation of the *ExactSumSweep* algorithm.
//!
//! The algorithm has been described by Michele Borassi, Pierluigi Crescenzi,
//! Michel Habib, Walter A. Kosters, Andrea Marino, and Frank W. Takes in “[Fast
//! diameter and radius BFS-based computation in (weakly connected) real-world
//! graphs–With an application to the six degrees of separation
//! games](https://www.sciencedirect.com/science/article/pii/S0304397515001644)”,
//! *Theoretical Computer Science*, 586:59–80, Elsevier, 2015. [DOI
//! 10.1016/j.tcs.2015.02.033](https://doi.org/10.1016/j.tcs.2015.02.033).
//!
//!
//! ```
//! use webgraph_algo::algo::exact_sum_sweep::{self, *};
//! use webgraph_algo::threads;
//! use dsi_progress_logger::no_logging;
//! use webgraph::graphs::vec_graph::VecGraph;
//! use webgraph::labels::proj::Left;
//!
//! let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 3), (3, 0), (2, 4)]));
//! let transpose = Left(VecGraph::from_arc_list([(1, 0), (2, 1), (3, 2), (0, 3), (4, 2)]));
//!
//! // Let's compute all eccentricities
//! let result = exact_sum_sweep::All::compute_directed(
//!     &graph,
//!     &transpose,
//!     None,
//!     &threads![],
//!     no_logging![]
//! );
//!
//! assert_eq!(result.diameter, 4);
//! assert_eq!(result.radius, 3);
//! assert_eq!(result.forward_eccentricities.as_ref(), &vec![3, 3, 3, 4, 0]);
//! assert_eq!(result.backward_eccentricities.as_ref(), &vec![3, 3, 3, 3, 4]);
//!
//! // Let's just compute the radius and diameter
//! let result = exact_sum_sweep::RadiusDiameter::compute_directed(
//!     &graph,
//!     &transpose,
//!     None,
//!     &threads![],
//!     no_logging![]
//! );
//!
//! assert_eq!(result.diameter, 4);
//! assert_eq!(result.radius, 3);
//! ```
//!
//! Note how certain information is not available if not computed.
//! ```compile_fail
//! use webgraph_algo::algo::exact_sum_sweep::{self, *};
//! use webgraph_algo::threads;
//! use dsi_progress_logger::no_logging;
//! use webgraph::graphs::vec_graph::VecGraph;
//! use webgraph::labels::proj::Left;
//!
//! let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 3), (3, 0), (2, 4)]));
//! let transpose = Left(VecGraph::from_arc_list([(1, 0), (2, 1), (3, 2), (0, 3), (4, 2)]));
//!
//! let result = exact_sum_sweep::RadiusDiameter::compute_directed(
//!     &graph,
//!     &transpose,
//!     None,
//!     &threads![],
//!     no_logging![]
//! );
//!
//! assert_eq!(result.diameter, 4);
//! assert_eq!(result.radius, 3);
//! // Without these it would compile
//! assert_eq!(result.forward_eccentricities.as_ref(), &vec![3, 3, 3, 4, 0]);
//! assert_eq!(result.backward_eccentricities.as_ref(), &vec![3, 3, 3, 3, 4]);
//! ```
//!
//! If the graph is undirected (symmetric), you may use [compute_undirected](OutputLevel::compute_undirected).
//! ```
//! use webgraph_algo::algo::exact_sum_sweep::{self, *};
//! use webgraph_algo::threads;
//! use dsi_progress_logger::no_logging;
//! use webgraph::graphs::vec_graph::VecGraph;
//! use webgraph::labels::proj::Left;
//!
//! let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 0), (1, 2), (2, 1), (2, 0), (0, 2), (3, 4), (4, 3)]));
//!
//! let result = exact_sum_sweep::RadiusDiameter::compute_undirected(
//!     &graph,
//!     &threads![],
//!     no_logging![]
//! );
//!
//! assert_eq!(result.diameter, 1);
//! assert_eq!(result.radius, 1);
//! ```

mod computer;
mod dir_outputs;
mod output_level;
mod scc_graph;
mod undir_outputs;

/// Module containing all result structures that may be produced as the results
/// of the *ExactSumSweep* algorithm.
pub mod outputs {
    use super::*;

    /// Module containing all result structures that may be produced as the results
    /// of the *ExactSumSweep* algorithm on undirected graphs.
    pub mod undirected {
        pub use super::undir_outputs::*;
    }

    /// Module containing all result structures that may be produced as the results
    /// of the *ExactSumSweep* algorithm on directed graphs.
    pub mod directed {
        pub use super::dir_outputs::*;
    }
}

pub use output_level::*;
