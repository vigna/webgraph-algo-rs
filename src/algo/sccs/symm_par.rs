// TODO: remove when done
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_mut)]
use std::mem::MaybeUninit;

use super::{StronglyConnectedComponents, StronglyConnectedComponentsNoT};
use crate::{
    algo::{self},
    prelude::breadth_first::{self, ParLowMem},
    threads,
    traits::Parallel,
};
use unwrap_infallible::UnwrapInfallible;
use webgraph::{labels::Left, prelude::VecGraph, utils::SyncSliceExt};

/// Connected components by Parallel visits on symmetric graphs.
pub struct SymmPar<A: algo::visits::Event, V: Parallel<A>> {
    num_comps: usize,
    component: Box<[usize]>,
    _marker: std::marker::PhantomData<(A, V)>,
}

impl<A: algo::visits::Event, V: Parallel<A>> StronglyConnectedComponents for SymmPar<A, V> {
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
        let mut visit = ParLowMem::new(&graph, 100);
        let mut component = vec![MaybeUninit::uninit(); graph.num_nodes()].into_boxed_slice();
        let mut number_of_components = 0;
        let slice = unsafe { component.as_sync_slice() };
        let threads = &threads![];

        for root in 0..graph.num_nodes() {
            /*visit
            .par_visit(
                root,
                |event| {
                    match event {
                        breadth_first::EventPred::Init { .. } => {}
                        breadth_first::EventPred::Unknown { curr, .. } => {
                            unsafe { slice.get_mut(curr).write(number_of_components) };
                        }
                        _ => (),
                    }
                    Ok(())
                },
                &threads,
                pl,
            )
            .unwrap_infallible();*/
            number_of_components += 1;
        }
        let component =
            unsafe { std::mem::transmute::<Box<[MaybeUninit<usize>]>, Box<[usize]>>(component) };

        SymmPar {
            component,
            num_comps: number_of_components + 1,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<A: algo::visits::Event, V: Parallel<A>> StronglyConnectedComponentsNoT for SymmPar<A, V> {
    fn compute(
        graph: impl webgraph::prelude::RandomAccessGraph,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Self {
        Self::compute_with_t(graph, Left(VecGraph::<()>::new()), pl)
    }
}
