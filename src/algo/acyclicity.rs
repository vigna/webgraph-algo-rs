use crate::{algo::visits::dfv::*, algo::visits::SeqVisit, algo::visits::StoppedWhenDone};
use dsi_progress_logger::ProgressLog;
use webgraph::traits::RandomAccessGraph;

/// Runs an acyclicity test.
pub fn run(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> bool {
    let mut visit = SingleThreadedDepthFirstVisit::<ThreeState, StoppedWhenDone, _>::new(&graph);
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Checking acyclicity");

    let acyclic = visit.visit(
        |&Args {
             curr: _curr,
             pred: _pred,
             root: _root,
             depth: _depth,
             event,
         }| {
            // Stop the visit as soon as a back edge is found.
            if event == Event::Revisit(true) {
                Err(StoppedWhenDone {})
            } else {
                Ok(())
            }
        },
        |_| true,
        pl,
    );

    pl.done();
    acyclic.is_ok()
}
