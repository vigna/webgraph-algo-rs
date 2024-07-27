use dsi_progress_logger::ProgressLogger;
use webgraph::prelude::BVGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::BFV;
use webgraph_algo::prelude::*;

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_cnr_2000_setup() -> usize {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .unwrap();
    graph.num_nodes()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_cnr_2000_sequential() {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .unwrap();
    let visit = BFV::new_sequential(&graph).with_start(10000).build();
    visit
        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
        .unwrap()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_cnr_2000_parallel() {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .unwrap();
    let visit = BFV::new_parallel(&graph)
        .with_start(10000)
        .with_granularity(32)
        .build();
    visit
        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
        .unwrap()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_cnr_2000_parallel_fast_callback() {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .unwrap();
    let visit = BFV::new_parallel_fast_callback(&graph)
        .with_start(10000)
        .with_granularity(32)
        .build();
    visit
        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
        .unwrap()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_in_2004_setup() -> usize {
    let graph = BVGraph::with_basename("tests/graphs/in-2004")
        .load()
        .unwrap();
    graph.num_nodes()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_in_2004_sequential() {
    let graph = BVGraph::with_basename("tests/graphs/in-2004")
        .load()
        .unwrap();
    let visit = BFV::new_sequential(&graph).with_start(10000).build();
    visit
        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
        .unwrap()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_in_2004_parallel() {
    let graph = BVGraph::with_basename("tests/graphs/in-2004")
        .load()
        .unwrap();
    let visit = BFV::new_parallel(&graph)
        .with_start(10000)
        .with_granularity(32)
        .build();
    visit
        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
        .unwrap()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_in_2004_parallel_fast_callback() {
    let graph = BVGraph::with_basename("tests/graphs/in-2004")
        .load()
        .unwrap();
    let visit = BFV::new_parallel_fast_callback(&graph)
        .with_start(10000)
        .with_granularity(32)
        .build();
    visit
        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
        .unwrap()
}

#[cfg(windows)]
fn main() {
    println!("iai not available on Windows. Skipping...");
}

#[cfg(not(windows))]
use iai::main;

#[cfg(not(windows))]
main!(
    test_bfv_cnr_2000_setup,
    test_bfv_cnr_2000_sequential,
    test_bfv_cnr_2000_parallel,
    test_bfv_cnr_2000_parallel_low_mem
    test_bfv_in_2004_setup,
    test_bfv_in_2004_sequential,
    test_bfv_in_2004_parallel,
    test_bfv_in_2004_parallel_low_mem
);
