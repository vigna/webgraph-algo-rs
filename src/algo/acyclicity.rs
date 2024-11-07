use crate::{
    algo::visits::depth_first::*, algo::visits::Sequential, algo::visits::StoppedWhenDone,
};
use dsi_progress_logger::ProgressLog;
use webgraph::traits::RandomAccessGraph;

use super::visits::NodePred;

/// Runs an acyclicity test.
pub fn run(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> bool {
    let mut visit = Seq::<NodePred, ThreeStates, StoppedWhenDone, _, _>::new(&graph);
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Checking acyclicity");

    let acyclic = visit.visit_all(
        |args| {
            // Stop the visit as soon as a back edge is found.
            match args.event {
                EventPred::Revisit(true) => Err(StoppedWhenDone {}),
                _ => Ok(()),
            }
        },
        pl,
    );

    pl.done();
    acyclic.is_ok()
}
