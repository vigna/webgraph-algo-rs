use dsi_progress_logger::ProgressLogger;
use webgraph::graphs::BVGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::*;
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
    let visit = SingleThreadedBreadthFirstVisit::with_start(&graph, 10000);
    visit
        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
        .unwrap()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_cnr_2000_parallel() {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .unwrap();
    let visit = ParallelBreadthFirstVisit::with_start(&graph, 10000);
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
    let visit = SingleThreadedBreadthFirstVisit::with_start(&graph, 10000);
    visit
        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
        .unwrap()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_in_2004_parallel() {
    let graph = BVGraph::with_basename("tests/graphs/in-2004")
        .load()
        .unwrap();
    let visit = ParallelBreadthFirstVisit::with_start(&graph, 10000);
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
    test_bfv_in_2004_setup,
    test_bfv_in_2004_sequential,
    test_bfv_in_2004_parallel,
);
