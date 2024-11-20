use super::BasicSccs;
use crate::{algo::top_sort, algo::visits::Sequential, prelude::depth_first::*};
use dsi_progress_logger::ProgressLog;
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

/// Computes the strongly connected components of a graph using Kosaraju's algorithm.
///
/// # Arguments
/// * `graph`: the graph.
/// * `transpose`: the transposed of `graph`.
/// * `pl`: a progress logger.
pub fn kosaraju(
    graph: impl RandomAccessGraph,
    transpose: impl RandomAccessGraph,
    pl: &mut impl ProgressLog,
) -> BasicSccs {
    let top_sort = top_sort::run(&graph, pl);
    let mut number_of_components = 0;
    let mut visit = SeqNoPred::new(&transpose);
    let mut components = vec![0; graph.num_nodes()].into_boxed_slice();

    for &node in &top_sort {
        visit
            .visit(
                node,
                |event| {
                    match event {
                        EventNoPred::Previsit { curr, .. } => {
                            components[curr] = number_of_components;
                        }
                        EventNoPred::Done { .. } => {
                            number_of_components += 1;
                        }
                        _ => (),
                    }
                    Ok(())
                },
                pl,
            )
            .unwrap_infallible();
    }
    BasicSccs::new(number_of_components, components)
}
