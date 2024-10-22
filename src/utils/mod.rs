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
pub use mmap_helper::{MmapHelper, MmapSlice, TempMmapOptions};

mod closure_vec;
pub use closure_vec::closure_vec;

mod hyper_log_log;
pub use hyper_log_log::{
    HyperLogLogCounter, HyperLogLogCounterArray, HyperLogLogCounterArrayBuilder, ThreadHelper,
};

mod threadpool;
pub(crate) use threadpool::Threads;

pub mod traits;

const MAX_NODES_ENV_VAR: &str = "MAX_TRANSPOSED_SIZE_DEBUG";
const MAX_NODES_DEFAULT: usize = 10000;

/// Returns whether `transposed` is the transposed graph of `graph`.
///
/// # Arguments
/// * `graph`: the direct graph.
/// * `transposed`: the graph to check whether is the transposed of `graph`.
pub(crate) fn check_transposed<G1: RandomAccessGraph, G2: RandomAccessGraph>(
    graph: &G1,
    transposed: &G2,
) -> bool {
    if graph.num_nodes() != transposed.num_nodes() || graph.num_arcs() != transposed.num_arcs() {
        return false;
    } else {
        let max_nodes = std::env::var(MAX_NODES_ENV_VAR)
            .map(|v| v.parse().unwrap_or(MAX_NODES_DEFAULT))
            .unwrap_or(MAX_NODES_DEFAULT);
        if graph.num_nodes() > max_nodes {
            eprintln!("This graph is bigger than {} nodes ({} nodes). It is assumed to be the correct transposed. If you wish to raise the maximum size to check at runtime, set the environment variable {} to the desired maximum size", max_nodes, graph.num_nodes(), MAX_NODES_ENV_VAR);
            return true;
        }
        for node in 0..graph.num_nodes() {
            for succ in graph.successors(node) {
                if !transposed
                    .successors(succ)
                    .into_iter()
                    .any(|pred| pred == node)
                {
                    return false;
                }
            }
        }
    }
    true
}
