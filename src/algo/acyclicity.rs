use crate::{algo::visits::dfv::*, algo::visits::SeqVisit};
use dsi_progress_logger::ProgressLog;
use webgraph::traits::RandomAccessGraph;

pub fn run(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> bool {
    let mut visit = SingleThreadedDepthFirstVisit::<ThreeState, _>::new(&graph);
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Checking acyclicity");

    let mut acyclic = true;

    visit.visit(
        |_| {},
        |&Args {
             node: _node,
             pred: _pred,
             root: _root,
             depth: _depth,
             event,
         }| {
            if let Event::Known(true) = event {
                acyclic = false;
                false
            } else {
                true
            }
        },
        pl,
    );

    pl.done();
    acyclic
}
