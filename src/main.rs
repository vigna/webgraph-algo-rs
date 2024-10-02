use anyhow::Result;
use dsi_progress_logger::{ProgressLog, ProgressLogger};
use epserde::deser::{Deserialize, Flags};
use webgraph::prelude::{BvGraph, DCF};
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::hyperball::*;
use webgraph_algo::prelude::*;
use webgraph_algo::utils::HyperLogLogCounterArrayBuilder;

fn main() -> Result<()> {
    stderrlog::new()
        .verbosity(2)
        .timestamp(stderrlog::Timestamp::Second)
        .init()?;
    let basename = std::env::args().nth(1).expect("No graph basename provided");
    let graph = BvGraph::with_basename(&basename).load()?;
    let reversed_graph = BvGraph::with_basename(basename.clone() + "-t").load()?;
    let cumulative = DCF::load_mmap(basename + ".dcf", Flags::empty())?;
    let main_pl = ProgressLogger::default();
    main_pl.info(format_args!("Starting test..."));

    let mut flags = MmapFlags::empty();
    flags.set(MmapFlags::SHARED, true);
    flags.set(MmapFlags::RANDOM_ACCESS, true);

    let mut hyper_ball_pl = ProgressLogger::default();
    hyper_ball_pl
        .display_memory(true)
        .local_speed(true)
        .log_interval(std::time::Duration::from_secs(180));
    let mut hyper_ball = HyperBallBuilder::new(&graph, cumulative.as_ref())
        .with_transposed(Some(&reversed_graph))
        .with_neighbourhood_function(true)
        .with_hyperloglog_settings(
            HyperLogLogCounterArrayBuilder::new()
                .with_log_2_num_registers(6)
                .with_num_elements_upper_bound(graph.num_nodes()),
        )
        .build(hyper_ball_pl.clone())?;
    hyper_ball.run_until_done(hyper_ball_pl)?;

    Ok(())
}
