//! Module containing implementations and builders for the *SumSweep* algorithm,
//! both for directed and undirected graphs.

mod scc_graph;

mod dir_sum_sweep;
pub use dir_sum_sweep::*;

mod undir_sum_sweep;
pub use undir_sum_sweep::*;

mod output;
pub use output::SumSweepOutputLevel;
