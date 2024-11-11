use crate::{algo::top_sort, algo::visits::Sequential, prelude::depth_first::*};
use common_traits::Integer;
use dsi_progress_logger::ProgressLog;
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

use super::traits::StronglyConnectedComponents;

/// Implementation of Kosaraju's algorithm to compute the strongly connected components
/// on a graph.
pub struct Kosaraju {
    n_of_components: usize,
    component: Vec<usize>,
}

impl StronglyConnectedComponents for Kosaraju {
    fn number_of_components(&self) -> usize {
        self.n_of_components
    }

    fn component(&self) -> &[usize] {
        self.component.as_ref()
    }

    fn component_mut(&mut self) -> &mut [usize] {
        self.component.as_mut()
    }
    fn compute(
        graph: impl RandomAccessGraph,
        transpose: impl RandomAccessGraph,
        pl: &mut impl ProgressLog,
    ) -> Self {
        let top_sort = top_sort::run(&graph, pl);
        let mut comp_index = 0.wrapping_sub(1);
        let mut visit = Seq::new(&transpose);
        let mut component = vec![0; graph.num_nodes()];

        for &node in &top_sort {
            visit
                .visit(
                    node,
                    |event| {
                        match event {
                            Event::Init { .. } => {
                                comp_index = comp_index.wrapping_add(1);
                            }
                            Event::Previsit { curr, .. } => {
                                component[curr] = comp_index;
                            }
                            _ => (),
                        }
                        Ok(())
                    },
                    pl,
                )
                .unwrap_infallible();
        }
        Kosaraju {
            component,
            n_of_components: comp_index + 1,
        }
    }

    fn compute_no_transpose(_graph: impl RandomAccessGraph, _pl: &mut impl ProgressLog) -> Self {
        unimplemented!()
    }
}
