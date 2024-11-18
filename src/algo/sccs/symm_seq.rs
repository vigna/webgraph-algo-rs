use super::StronglyConnectedComponents;
use crate::{prelude::depth_first, traits::Sequential};
use dsi_progress_logger::ProgressLog;
use std::mem::MaybeUninit;
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

/// Connected components by sequential visits on symmetric graphs.
pub struct SymmSeq {
    num_components: usize,
    component: Box<[usize]>,
}

impl SymmSeq {
    pub fn compute(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Self {
        // debug_assert!(check_symmetric(&graph)); requires sync
        let mut visit = depth_first::Seq::new(&graph);
        let mut component = vec![MaybeUninit::uninit(); graph.num_nodes()].into_boxed_slice();
        let mut number_of_components = 0usize.wrapping_sub(1);

        visit
            .visit_all(
                |event| {
                    match event {
                        depth_first::Event::Init { .. } => {
                            number_of_components = number_of_components.wrapping_add(1);
                        }
                        depth_first::Event::Previsit { curr, .. } => {
                            component[curr].write(number_of_components);
                        }
                        _ => (),
                    }
                    Ok(())
                },
                pl,
            )
            .unwrap_infallible();

        let component =
            unsafe { std::mem::transmute::<Box<[MaybeUninit<usize>]>, Box<[usize]>>(component) };

        SymmSeq {
            component,
            num_components: number_of_components + 1,
        }
    }
}

impl StronglyConnectedComponents for SymmSeq {
    fn num_components(&self) -> usize {
        self.num_components
    }

    fn component(&self) -> &[usize] {
        &self.component
    }

    fn component_mut(&mut self) -> &mut [usize] {
        &mut self.component
    }
}
