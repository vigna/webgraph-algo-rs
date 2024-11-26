use crate::{
    prelude::{
        breadth_first::{EventNoPred, ParFairNoPred},
        sccs::BasicSccs,
        Parallel,
    },
    utils::*,
};
use dsi_progress_logger::ProgressLog;
use rayon::ThreadPool;
use std::{
    mem::MaybeUninit,
    sync::atomic::{AtomicUsize, Ordering},
};
use sync_cell_slice::SyncSlice;
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

/// Connected components of symmetric graphs by parallel visits.
pub fn symm_par(
    graph: impl RandomAccessGraph + Sync,
    thread_pool: &ThreadPool,
    pl: &mut impl ProgressLog,
) -> BasicSccs {
    debug_assert!(check_symmetric(&graph));

    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Computing strongly connected components...");

    // TODO: use a better value for granularity
    let mut visit = ParFairNoPred::new(&graph, 100);
    let mut component = Box::new_uninit_slice(num_nodes);

    let number_of_components = AtomicUsize::new(0);
    let slice = component.as_sync_slice();

    visit
        .par_visit_all(
            |event| {
                match event {
                    EventNoPred::Init { .. } => {}
                    EventNoPred::Unknown { curr, .. } => {
                        unsafe {
                            slice[curr].set(MaybeUninit::new(
                                number_of_components.load(Ordering::Relaxed),
                            ))
                        };
                    }
                    EventNoPred::Done { .. } => {
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

    let component = unsafe { component.assume_init() };

    pl.done();

    BasicSccs::new(number_of_components.load(Ordering::Relaxed), component)
}
