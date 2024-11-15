use super::traits::{StronglyConnectedComponents, StronglyConnectedComponentsNoT};
use crate::{prelude::depth_first, traits::Sequential, utils::check_symmetric};
use unwrap_infallible::UnwrapInfallible;
use webgraph::{labels::Left, prelude::VecGraph};

pub struct SymDepthFirst {
    num_comps: usize,
    component: Vec<usize>,
}

impl StronglyConnectedComponents for SymDepthFirst {
    fn num_components(&self) -> usize {
        self.num_comps
    }

    fn component(&self) -> &[usize] {
        &self.component
    }

    fn component_mut(&mut self) -> &mut [usize] {
        &mut self.component
    }

    fn compute_with_t(
        graph: impl webgraph::prelude::RandomAccessGraph,
        _transpose: impl webgraph::prelude::RandomAccessGraph,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Self {
        // debug_assert!(check_symmetric(&graph)); requires sync
        let mut visit = depth_first::Seq::new(&graph);
        let mut component = vec![0; graph.num_nodes()];
        let mut number_of_components = 0usize.wrapping_sub(1);

        visit
            .visit_all(
                |event| {
                    match event {
                        depth_first::Event::Init { .. } => {
                            number_of_components = number_of_components.wrapping_add(1);
                        }
                        depth_first::Event::Previsit { curr, .. } => {
                            component[curr] = number_of_components;
                        }
                        _ => (),
                    }
                    Ok(())
                },
                pl,
            )
            .unwrap_infallible();

        SymDepthFirst {
            component,
            num_comps: number_of_components + 1,
        }
    }
}

impl StronglyConnectedComponentsNoT for SymDepthFirst {
    fn compute(
        graph: impl webgraph::prelude::RandomAccessGraph,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Self {
        Self::compute_with_t(graph, Left(VecGraph::<()>::new()), pl)
    }
}
