use crate::{
    prelude::breadth_first::{Event, EventPred, ParFair, ParLowMem},
    traits::{BasicSccs, Parallel},
    utils::*,
};
use dsi_progress_logger::ProgressLog;
use rayon::ThreadPool;
use std::mem::MaybeUninit;
use unwrap_infallible::UnwrapInfallible;
use webgraph::{traits::RandomAccessGraph, utils::SyncSliceExt};

/// Connected components of symmetric graphs by parallel visits.
pub fn symm_par(
    graph: impl RandomAccessGraph + Sync,
    thread_pool: &ThreadPool,
    pl: &mut impl ProgressLog,
) -> BasicSccs {
    debug_assert!(check_symmetric(&graph));
    // TODO: use a better value for granularity
    let mut visit = ParLowMem::new(&graph, 100);
    let mut component = vec![MaybeUninit::uninit(); graph.num_nodes()].into_boxed_slice();
    let mut number_of_components = 0;
    let slice = unsafe { component.as_sync_slice() };

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
                thread_pool,
                pl,
            )
            .unwrap_infallible();
        number_of_components += 1;
    }
    let component =
        unsafe { std::mem::transmute::<Box<[MaybeUninit<usize>]>, Box<[usize]>>(component) };

    BasicSccs::new(number_of_components + 1, component)
}
