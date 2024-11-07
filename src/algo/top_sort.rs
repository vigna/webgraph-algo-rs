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

    let mut topol_sort = vec![MaybeUninit::uninit(); num_nodes];
    let mut pos = num_nodes;

    visit
        .visit_all(
            |args| {
                if let EventPred::Postvisit { curr, .. } = args {
                    pos -= 1;
                    topol_sort[pos].write(curr);
                }

                Ok(())
            },
            pl,
        )
        .unwrap_infallible();

    pl.done();
    // SAFETY: we write in each element of top_sort
    unsafe { std::mem::transmute::<Vec<MaybeUninit<usize>>, Vec<usize>>(topol_sort) }
        .into_boxed_slice()
}
