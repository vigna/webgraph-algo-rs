use anyhow::Result;
use dsi_progress_logger::{ProgressLog, ProgressLogger};
use webgraph::graphs::BVGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::*;
use webgraph_algo::prelude::*;

fn main() -> Result<()> {
    stderrlog::new().verbosity(2).init()?;
    let graph =
        BVGraph::with_basename(std::env::args().nth(1).expect("No graph basename provided"))
            .load()?;
    let start = std::env::args()
        .nth(2)
        .unwrap_or("0".to_string())
        .parse()
        .expect("No valid index provided");
    let main_pl = ProgressLogger::default();
    main_pl.info(format_args!("Starting test..."));

    let webgraph_visit = webgraph::algo::BfsOrder::new(&graph);
    let webgraph_order = webgraph_visit.collect::<Vec<_>>();

    let sequential_visit = SingleThreadedBreadthFirstVisit::with_start(&graph, start);
    let mut sequential_pl = ProgressLogger::default();
    sequential_pl.display_memory(true).local_speed(true);
    let sequential_result = sequential_visit.visit(sequential_pl)?;
    let sequential_order = sequential_result.order;

    assert_eq!(sequential_order.len(), graph.num_nodes());
    assert_eq!(webgraph_order.len(), graph.num_nodes());

    Ok(())
}
