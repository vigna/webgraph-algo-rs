use webgraph::traits::RandomAccessGraph;

mod argmax;
mod argmin;

/// Module containing mathematical utilities.
pub mod math {
    pub use super::argmax::*;
    pub use super::argmin::*;
}

mod mmap_slice;
#[doc(hidden)]
pub use mmap_slice::MmapFlags;
pub use mmap_slice::{MmapSlice, TempMmapOptions};

mod closure_vec;
pub use closure_vec::closure_vec;

mod hyper_log_log;
pub use hyper_log_log::{
    HyperLogLogCounter, HyperLogLogCounterArray, HyperLogLogCounterArrayBuilder, ThreadHelper,
};

pub mod traits;

/// Returns whether `transposed` is the transposed graph of `graph`.
///
/// # Arguments
/// - `graph`: the direct graph.
/// - `transposed`: the graph to check whether is the transposed of `graph`.
pub(crate) fn check_transposed<G1: RandomAccessGraph, G2: RandomAccessGraph>(
    graph: &G1,
    transposed: &G2,
) -> bool {
    if graph.num_nodes() != transposed.num_nodes() {
        return false;
    } else if graph.num_arcs() != transposed.num_arcs() {
        return false;
    } else {
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
    return true;
}
