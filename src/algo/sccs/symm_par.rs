use crate::{
    prelude::breadth_first::{Event, ParFair},
    traits::{BasicSccs, Parallel},
    utils::*,
};
use dsi_progress_logger::ProgressLog;
use rayon::ThreadPool;
use std::{mem::MaybeUninit, sync::atomic::*};
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
    let mut visit = ParFair::new(&graph, 100);
    let mut component = vec![MaybeUninit::uninit(); graph.num_nodes()].into_boxed_slice();
    let mut number_of_components = 0;
    let update_counter = AtomicBool::new(false);
    let slice = unsafe { component.as_sync_slice() };

    for root in 0..graph.num_nodes() {
        visit
            .par_visit(
                root,
                |event| {
                    match event {
                        Event::Init { .. } => update_counter.store(true, Ordering::Relaxed),
                        Event::Unknown { curr, .. } => {
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
        if update_counter.swap(false, Ordering::Relaxed) {
            number_of_components += 1;
        }
    }
    let component =
        unsafe { std::mem::transmute::<Box<[MaybeUninit<usize>]>, Box<[usize]>>(component) };

    BasicSccs::new(number_of_components, component)
}
