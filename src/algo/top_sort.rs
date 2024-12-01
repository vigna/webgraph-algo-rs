use crate::{algo::visits::depth_first::*, algo::visits::Sequential};
use dsi_progress_logger::ProgressLog;
use no_break::NoBreak;
use std::ops::ControlFlow::Continue;
use webgraph::traits::RandomAccessGraph;

/// Returns the node of the graph in topological-sort order, if the graph is acyclic.
///
/// Otherwise, the order reflects the exit times from a depth-first visit of the graph.
pub fn top_sort(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Box<[usize]> {
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Computing topological sort");

    let mut visit = SeqPred::new(&graph);
    let mut topol_sort = Box::new_uninit_slice(num_nodes);
    let mut pos = num_nodes;

    visit
        .visit_all(
            |event| {
                if let EventPred::Postvisit { curr, .. } = event {
                    pos -= 1;
                    topol_sort[pos].write(curr);
                }

                Continue(())
            },
            pl,
        )
        .continue_value_no_break();

    pl.done();
    // SAFETY: we write in each element of top_sort
    unsafe { topol_sort.assume_init() }
}
