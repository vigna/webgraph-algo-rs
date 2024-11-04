use crate::{algo::visits::dfv::*, algo::visits::SeqVisit};
use dsi_progress_logger::ProgressLog;
use std::mem::MaybeUninit;
use webgraph::traits::RandomAccessGraph;

/// Returns the node of the graph in topological-sort order, if the graph is acyclic.
///
/// Otherwise, the order reflects the exit times from a depth-first visit of the graph.
pub fn run(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Box<[usize]> {
    let mut visit =
        SingleThreadedDepthFirstVisit::<TwoState, std::convert::Infallible, _>::new(&graph);
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Computing topological sort");

    let mut top_sort = vec![MaybeUninit::uninit(); num_nodes];
    let mut pos = num_nodes;

    visit.visit(
        |&Args {
             node,
             pred: _pred,
             root: _root,
             depth: _depth,
             event,
         }| {
            match event {
                Event::Completed => {
                    pos -= 1;
                    top_sort[pos].write(node);
                }
                _ => {}
            }

            Ok(())
        },
        |_| true,
        pl,
    );

    pl.done();
    // SAFETY: we write in each element of top_sort
    unsafe { std::mem::transmute::<_, Vec<usize>>(top_sort) }.into_boxed_slice()
}
