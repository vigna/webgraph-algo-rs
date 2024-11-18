use super::StronglyConnectedComponents;
use crate::{
    prelude::breadth_first::{EventPred, ParLowMem},
    threads,
    traits::Parallel,
    utils::*,
};
use dsi_progress_logger::ProgressLog;
use std::mem::MaybeUninit;
use unwrap_infallible::UnwrapInfallible;
use webgraph::{traits::RandomAccessGraph, utils::SyncSliceExt};

/// Connected components by Parallel visits on symmetric graphs.
pub struct SymmPar {
    num_comps: usize,
    component: Box<[usize]>,
}

impl SymmPar {
    pub fn compute(graph: impl RandomAccessGraph + Sync, pl: &mut impl ProgressLog) -> Self {
        debug_assert!(check_symmetric(&graph));
        let mut visit = ParLowMem::new(&graph, 100);
        let mut component = vec![MaybeUninit::uninit(); graph.num_nodes()].into_boxed_slice();
        let mut number_of_components = 0;
        let slice = unsafe { component.as_sync_slice() };
        let threads = threads![];

        for root in 0..graph.num_nodes() {
            visit
                .par_visit(
                    root,
                    |event| {
                        match event {
                            EventPred::Init { .. } => {}
                            EventPred::Unknown { curr, .. } => {
                                slice.set(curr, MaybeUninit::new(number_of_components));
                            }
                            _ => (),
                        }
                        Ok(())
                    },
                    &threads,
                    pl,
                )
                .unwrap_infallible();
            number_of_components += 1;
        }
        let component =
            unsafe { std::mem::transmute::<Box<[MaybeUninit<usize>]>, Box<[usize]>>(component) };

        SymmPar {
            component,
            num_comps: number_of_components + 1,
        }
    }
}

impl StronglyConnectedComponents for SymmPar {
    fn num_components(&self) -> usize {
        self.num_comps
    }

    fn component(&self) -> &[usize] {
        &self.component
    }

    fn component_mut(&mut self) -> &mut [usize] {
        &mut self.component
    }
}
