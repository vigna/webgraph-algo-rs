use crate::{algo::visits::dfv::*, algo::visits::SeqVisit};
use dsi_progress_logger::ProgressLog;
use webgraph::traits::RandomAccessGraph;

pub fn run(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Box<[usize]> {
    let mut visit = SingleThreadedDepthFirstVisit::<TwoState, _>::new(&graph);
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Computing topological sort");

    let mut top_sort = vec![0; num_nodes];
    let mut pos = num_nodes;

    visit.visit(
        |Args {
             node,
             pred: _pred,
             root: _root,
             depth: _depth,
             event,
         }| {
            match event {
                Event::Completed => {
                    pos -= 1;
                    top_sort[pos] = node;
                }
                _ => {}
            }
        },
        |_| true,
        pl,
    );

    pl.done();
    top_sort.into()
}
