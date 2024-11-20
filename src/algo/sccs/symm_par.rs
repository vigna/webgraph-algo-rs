use crate::{
    prelude::breadth_first::{EventPred, ParLowMem},
    traits::{BasicSccs, Parallel},
    utils::*,
};
use dsi_progress_logger::ProgressLog;
use rayon::ThreadPool;
use std::{
    mem::MaybeUninit,
    sync::atomic::{AtomicUsize, Ordering},
};
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

    let number_of_components = AtomicUsize::new(0);
    let slice = unsafe { component.as_sync_slice() };

    visit
        .par_visit_all(
            |event| {
                match event {
                    EventPred::Init { .. } => {}
                    EventPred::Unknown { curr, .. } => {
                        slice.set(
                            curr,
                            MaybeUninit::new(number_of_components.load(Ordering::Relaxed)),
                        );
                    }
                    EventPred::Done { .. } => {
                        number_of_components.fetch_add(1, Ordering::Relaxed);
                    }
                    _ => (),
                }
                Ok(())
            },
            thread_pool,
            pl,
        )
        .unwrap_infallible();

    let component =
        unsafe { std::mem::transmute::<Box<[MaybeUninit<usize>]>, Box<[usize]>>(component) };

    BasicSccs::new(number_of_components.load(Ordering::Relaxed), component)
}
