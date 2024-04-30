use anyhow::Result;
use dsi_progress_logger::{ProgressLog, ProgressLogger};
use webgraph::graphs::BVGraph;
use webgraph_algo::algo::bfv::*;
use webgraph_algo::algo::diameter::*;
use webgraph_algo::prelude::*;

fn main() -> Result<()> {
    stderrlog::new().verbosity(2).init()?;
    let basename = std::env::args().nth(1).expect("No graph basename provided");
    let graph = BVGraph::with_basename(&basename).load()?;
    let reversed_graph = BVGraph::with_basename(basename + "-t").load()?;
    let start = std::env::args()
        .nth(2)
        .unwrap_or("0".to_string())
        .parse()
        .expect("No valid index provided");
    let sequential = std::env::args()
        .nth(3)
        .unwrap_or("true".to_string())
        .parse()
        .expect("No valid bool provided");
    let main_pl = ProgressLogger::default();
    main_pl.info(format_args!("Starting test..."));

    if sequential {
        let sequential_visit = SingleThreadedBreadthFirstVisit::with_start(&graph, start);
        let mut sequential_pl = ProgressLogger::default();
        sequential_pl.display_memory(true).local_speed(true);
        sequential_visit.visit(|_, _| {}, sequential_pl)?;
    }

    let parallel_visit = ParallelBreadthFirstVisit::with_parameters(&graph, start, 1);
    let mut parallel_pl = ProgressLogger::default();
    parallel_pl.display_memory(true).local_speed(true);
    parallel_visit.visit(|_, _| {}, parallel_pl)?;

    let parallel_visit = ParallelBreadthFirstVisit::with_parameters(&graph, start, 16);
    let mut parallel_pl = ProgressLogger::default();
    parallel_pl.display_memory(true).local_speed(true);
    parallel_visit.visit(|_, _| {}, parallel_pl)?;

    let parallel_visit = ParallelBreadthFirstVisit::with_parameters(&graph, start, 32);
    let mut parallel_pl = ProgressLogger::default();
    parallel_pl.display_memory(true).local_speed(true);
    parallel_visit.visit(|_, _| {}, parallel_pl)?;

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &reversed_graph,
        SumSweepOutputLevel::RadiusDiameter,
        None,
    )?;
    let mut sum_sweep_pl = ProgressLogger::default();
    sum_sweep_pl.display_memory(true).local_speed(true);
    sum_sweep.compute(sum_sweep_pl)?;
    main_pl.info(format_args!(
        "Diameter: {:?}\tRadius: {:?}",
        sum_sweep.diameter(),
        sum_sweep.radius()
    ));

    Ok(())
}
