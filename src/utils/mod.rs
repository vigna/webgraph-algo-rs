//! Module containing various utilities.
//!
//! Mostly for internal use, some structures may be useful outside of this crate.

use rayon::prelude::*;
use webgraph::traits::RandomAccessGraph;

mod argmax;
mod argmin;

/// Module containing mathematical utilities.
pub mod math {
    pub use super::argmax::*;
    pub use super::argmin::*;
}

mod mmap_helper;
#[doc(hidden)]
pub use mmap_helper::MmapFlags;
pub use mmap_helper::*;

/// Module containing implementations of the `HyperLogLog` algorithm
/// and implementing efficient Vecs of counters.
pub mod hyper_log_log;
pub use hyper_log_log::DefaultCounter;

/// Module containing utility traits.
pub mod traits;

/// Utility macro to return an `Ok::<_, Infallible>`.
///
/// There are two forms of this macro:
/// * Create an `Ok::<(), Infallible>`:
/// ```
/// # use webgraph_algo::ok_infallible;
/// let ok: Result::<(), std::convert::Infallible> = ok_infallible!();
/// assert!(ok.is_ok());
/// assert_eq!(ok.unwrap(), ());
/// ```
/// * Create an `Ok::<_, Infallible>` from a given value:
/// ```
/// # use webgraph_algo::ok_infallible;
/// let value: usize = 42;
/// let ok: Result::<usize, std::convert::Infallible> = ok_infallible!(value);
/// assert!(ok.is_ok());
/// assert_eq!(ok.unwrap(), value);
/// ```
#[macro_export]
macro_rules! ok_infallible {
    () => {
        Ok::<(), std::convert::Infallible>(())
    };
    ($value:expr) => {
        Ok::<_, std::convert::Infallible>($value)
    };
}

/// Utility macro to create [`thread_pools`](`rayon::ThreadPool`).
///
/// There are two forms of this macro:
/// * Create a thread_pool with default setting:
/// ```
/// # use webgraph_algo::threads;
/// let t: rayon::ThreadPool = threads![];
/// ```
/// * Create a thread_pool with the given number of threads:
/// ```
/// # use webgraph_algo::threads;
/// let t: rayon::ThreadPool = threads![7];
/// assert_eq!(t.current_num_threads(), 7);
/// ```
#[macro_export]
macro_rules! threads {
    () => {
        rayon::ThreadPoolBuilder::new()
            .build()
            .expect("Should be able to build a thread_pool with default parameters")
    };
    ($num_threads:expr) => {
        rayon::ThreadPoolBuilder::new()
            .num_threads($num_threads)
            .build()
            .unwrap_or_else(|_| {
                panic!(
                    "Should be able to build a thread_pool with default parameters and {} threads",
                    $num_threads,
                )
            })
    };
}

const MAX_NODES_ENV_VAR: &str = "MAX_GRAPH_SIZE_DEBUG";
const MAX_NODES_DEFAULT: usize = 100_000;

/// Returns whether `transposed` is the transposed graph of `graph`.
///
/// # Arguments
/// * `graph`: the direct graph.
/// * `transposed`: the graph to check whether is the transposed of `graph`.
pub(crate) fn check_transposed<G1: RandomAccessGraph + Sync, G2: RandomAccessGraph + Sync>(
    graph: G1,
    transposed: G2,
) -> bool {
    if graph.num_nodes() != transposed.num_nodes() || graph.num_arcs() != transposed.num_arcs() {
        return false;
    }
    let max_nodes = std::env::var(MAX_NODES_ENV_VAR)
        .map(|v| v.parse().unwrap_or(MAX_NODES_DEFAULT))
        .unwrap_or(MAX_NODES_DEFAULT);
    if graph.num_nodes() > max_nodes {
        eprintln!("This graph is bigger than {} nodes ({} nodes). It is assumed to be the correct transposed. If you wish to raise the maximum size to check at runtime, set the environment variable {} to the desired maximum size", max_nodes, graph.num_nodes(), MAX_NODES_ENV_VAR);
        return true;
    }
    (0..graph.num_nodes())
        .into_par_iter()
        .try_for_each(|node| {
            for succ in graph.successors(node) {
                if !transposed
                    .successors(succ)
                    .into_iter()
                    .any(|pred| pred == node)
                {
                    return Err(());
                }
            }
            for succ in transposed.successors(node) {
                if !graph.successors(succ).into_iter().any(|pred| pred == node) {
                    return Err(());
                }
            }
            Ok(())
        })
        .is_ok()
}

/// Returns whether the graph is symmetric (can be considered undirected).
///
/// # Arguments
/// * `graph`: the graph.
pub(crate) fn check_symmetric<G: RandomAccessGraph + Sync>(graph: G) -> bool {
    let max_nodes = std::env::var(MAX_NODES_ENV_VAR)
        .map(|v| v.parse().unwrap_or(MAX_NODES_DEFAULT))
        .unwrap_or(MAX_NODES_DEFAULT);
    if graph.num_nodes() > max_nodes {
        eprintln!("This graph is bigger than {} nodes ({} nodes). It is assumed to be symmetric. If you wish to raise the maximum size to check at runtime, set the environment variable {} to the desired maximum size", max_nodes, graph.num_nodes(), MAX_NODES_ENV_VAR);
        return true;
    }
    (0..graph.num_nodes())
        .into_par_iter()
        .try_for_each(|node| {
            for succ in graph.successors(node) {
                if !graph.successors(succ).into_iter().any(|pred| pred == node) {
                    return Err(());
                }
            }
            Ok(())
        })
        .is_ok()
}
