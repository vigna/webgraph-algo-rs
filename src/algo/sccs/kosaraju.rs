use super::BasicSccs;
use crate::{algo::top_sort, algo::visits::Sequential, prelude::depth_first::*};
use common_traits::Integer;
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
    let mut number_of_components = 0.wrapping_sub(1);
    let mut visit = Seq::new(&transpose);
    let mut components = vec![0; graph.num_nodes()].into_boxed_slice();

    for &node in &top_sort {
        visit
            .visit(
                node,
                |event| {
                    match event {
                        Event::Init { .. } => {
                            number_of_components = number_of_components.wrapping_add(1);
                        }
                        Event::Previsit { curr, .. } => {
                            components[curr] = number_of_components;
                        }
                        _ => (),
                    }
                    Ok(())
                },
                pl,
            )
            .unwrap_infallible();
    }
    BasicSccs::new(number_of_components + 1, components)
}
