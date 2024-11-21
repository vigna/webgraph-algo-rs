use crate::{
    algo::visits::depth_first::*, algo::visits::Sequential, algo::visits::StoppedWhenDone,
};
use dsi_progress_logger::ProgressLog;
use webgraph::traits::RandomAccessGraph;

/// Runs an acyclicity test.
pub fn acyclicity(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> bool {
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Checking acyclicity");

    let mut visit = SeqPath::new(&graph);

    let acyclic = visit.visit_all(
        |event| {
            // Stop the visit as soon as a back edge is found.
            match event {
                EventPred::Revisit { on_stack: true, .. } => Err(StoppedWhenDone {}),
                _ => Ok(()),
            }
        },
        pl,
    );

    pl.done();
    acyclic.is_ok()
}
