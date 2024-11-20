use anyhow::Result;
use dsi_progress_logger::prelude::*;
use epserde::deser::{Deserialize, Flags};
use webgraph::prelude::{BvGraph, DCF};
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::hyperball::*;
use webgraph_algo::algo::{exact_sum_sweep::*, sccs};
use webgraph_algo::prelude::*;
use webgraph_algo::threads;
use webgraph_algo::utils::HyperLogLogCounterArrayBuilder;

fn main() -> Result<()> {
    stderrlog::new()
        .verbosity(2)
        .timestamp(stderrlog::Timestamp::Second)
        .init()?;
    let basename = std::env::args().nth(2).expect("No graph basename provided");
    let graph = BvGraph::with_basename(&basename).load()?;
    let mut main_pl = progress_logger![display_memory = true];
    main_pl.info(format_args!("Starting test..."));

    let mut flags = MmapFlags::empty();
    flags.set(MmapFlags::SHARED, true);
    flags.set(MmapFlags::RANDOM_ACCESS, true);

    let mem_options = TempMmapOptions::Default;

    match std::env::args()
        .nth(1)
        .expect("No operation provided")
        .as_str()
    {
        "tarjan" => {
            sccs::tarjan(&graph, &mut main_pl);
        }
        "diameter" => {
            let reversed_graph = BvGraph::with_basename(basename.clone() + "-t").load()?;
            RadiusDiameter::compute_directed(
                &graph,
                &reversed_graph,
                None,
                &threads![],
                &mut main_pl,
            );
        }
        "hyperball" => {
            let cumulative = DCF::load_mmap(basename.clone() + ".dcf", Flags::empty())?;
            let reversed_graph = BvGraph::with_basename(basename.clone() + "-t").load()?;
            let log2m = std::env::args()
                .nth(3)
                .expect("No log2m value provided")
                .parse()
                .expect("Expected integer");

            let mut hyperball = HyperBallBuilder::new(&graph, cumulative.as_ref())
                .hyperloglog_settings(
                    HyperLogLogCounterArrayBuilder::new()
                        .log_2_num_registers(log2m)
                        .mem_options(mem_options.clone())
                        .num_elements_upper_bound(graph.num_nodes()),
                )
                .sum_of_distances(true)
                .sum_of_inverse_distances(true)
                .transposed(Some(&reversed_graph))
                .build(&mut main_pl)?;
            hyperball.run_until_done(&threads![], &mut main_pl)?;
        }
        _ => panic!(),
    }

    Ok(())
}
