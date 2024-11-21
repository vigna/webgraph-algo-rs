use crate::{algo::visits::depth_first::*, algo::visits::Sequential};
use dsi_progress_logger::ProgressLog;
use std::mem::MaybeUninit;
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

/// Returns the node of the graph in topological-sort order, if the graph is acyclic.
///
/// Otherwise, the order reflects the exit times from a depth-first visit of the graph.
pub fn run(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Box<[usize]> {
    let mut visit = SeqPred::new(&graph);
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Computing topological sort");

    let mut topol_sort = vec![MaybeUninit::uninit(); num_nodes].into_boxed_slice();
    let mut pos = num_nodes;

    visit
        .visit_all(
            |event| {
                if let EventPred::Postvisit { curr, .. } = event {
                    pos -= 1;
                    topol_sort[pos].write(curr);
                }

                Ok(())
            },
            pl,
        )
        .unwrap_infallible();

    pl.done();
    let mut topol_sort = std::mem::ManuallyDrop::new(topol_sort);
    // SAFETY: we write in each element of top_sort
    unsafe { Box::from_raw(topol_sort.as_mut() as *mut [MaybeUninit<_>] as *mut [usize]) }
}
