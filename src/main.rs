/*
 * SPDX-FileCopyrightText: 2024 Matteo Dell'Acqua
 * SPDX-FileCopyrightText: 2025 Sebastiano Vigna
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

use anyhow::Result;
use dsi_progress_logger::prelude::*;
use epserde::deser::{Deserialize, Flags};
use webgraph::prelude::{BvGraph, LoadMem, DCF};
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::hyperball::*;
use webgraph_algo::algo::{exact_sum_sweep::*, sccs};
use webgraph_algo::prelude::*;
use webgraph_algo::threads;
use webgraph_algo::utils::hyper_log_log::HyperLogLogBuilder;
use webgraph_algo::utils::SliceCounterArray;

fn main2() -> Result<()> {
    stderrlog::new()
        .verbosity(2)
        .timestamp(stderrlog::Timestamp::Second)
        .init()?;
    let basename = std::env::args().nth(2).expect("No graph basename provided");
    let mut main_pl = concurrent_progress_logger![display_memory = true];
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
            let graph = BvGraph::with_basename(&basename).mode::<LoadMem>().load()?;
            sccs::tarjan(&graph, &mut main_pl);
        }
        "diameter" => {
            let graph = BvGraph::with_basename(&basename).load()?;
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
            let graph = BvGraph::with_basename(&basename).load()?;
            let cumulative = DCF::load_mmap(basename.clone() + ".dcf", Flags::empty())?;
            let transpose = BvGraph::with_basename(basename.clone() + "-t").load()?;
            let log2m = std::env::args()
                .nth(3)
                .expect("No log2m value provided")
                .parse()
                .expect("Expected integer");

            let hyper_log_log = HyperLogLogBuilder::new(graph.num_nodes())
                .log_2_num_reg(log2m)
                .build()?;
            let bits = SliceCounterArray::with_mmap(
                hyper_log_log.clone(),
                graph.num_nodes(),
                mem_options.clone(),
            )?;
            let result_bits = SliceCounterArray::with_mmap(
                hyper_log_log,
                graph.num_nodes(),
                mem_options.clone(),
            )?;
            let mut hyperball = HyperBallBuilder::with_transpose(
                &graph,
                &transpose,
                cumulative.as_ref(),
                bits,
                result_bits,
            )
            .sum_of_distances(true)
            .sum_of_inverse_distances(true)
            .build(&mut main_pl);
            hyperball.run_until_done(&threads![], &mut main_pl)?;
        }
        _ => panic!(),
    }

    Ok(())
}

fn main() {
    let mut v = vec![0; 5];
    let node = 0;
    let mut iter = (0..5).into_iter();
    while let Some(curr) = iter.next() {
        v[curr] = node;
    }
    println!("{:?}", v);
}
