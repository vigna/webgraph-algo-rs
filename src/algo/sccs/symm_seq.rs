use super::BasicSccs;
use crate::{algo::visits::Done, prelude::depth_first, traits::Sequential};
use dsi_progress_logger::ProgressLog;
use std::ops::ControlFlow::Continue;
use webgraph::traits::RandomAccessGraph;

/// Connected components of symmetric graphs by sequential visits.
pub fn symm_seq(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> BasicSccs {
    // debug_assert!(check_symmetric(&graph)); requires sync

    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Computing strongly connected components...");

    let mut visit = depth_first::SeqNoPred::new(&graph);
    let mut component = Box::new_uninit_slice(num_nodes);
    let mut number_of_components = 0;

    visit
        .visit_all(
            |event| {
                match event {
                    depth_first::EventNoPred::Previsit { curr, .. } => {
                        component[curr].write(number_of_components);
                    }
                    depth_first::EventNoPred::Done { .. } => {
                        number_of_components += 1;
                    }
                    _ => (),
                }
                Continue(())
            },
            pl,
        )
        .done();

    let component = unsafe { component.assume_init() };

    pl.done();

    BasicSccs::new(number_of_components, component)
}
