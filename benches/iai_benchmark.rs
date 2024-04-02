use dsi_progress_logger::ProgressLogger;
use webgraph::graphs::BVGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::*;
use webgraph_algo::prelude::*;

struct Node {
    index: usize,
}

struct Factory {}

impl NodeVisit for Node {
    type VisitResult = usize;
    type AccumulatedResult = Vec<usize>;

    fn visit(self) -> Self::VisitResult {
        self.index
    }

    fn init_result() -> Self::AccumulatedResult {
        Vec::new()
    }

    fn accumulate_result(
        partial_result: &mut Self::AccumulatedResult,
        visit_result: Self::VisitResult,
    ) {
        partial_result.push(visit_result)
    }
}

impl NodeFactory for Factory {
    type Node = Node;

    fn node_from_index(&self, node_index: usize) -> Self::Node {
        Node { index: node_index }
    }
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_cnr_2000_setup() -> (usize, Node) {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .unwrap();
    let factory = Factory {};
    (graph.num_nodes(), factory.node_from_index(10000))
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_cnr_2000_sequential() -> Vec<usize> {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .unwrap();
    let factory = Factory {};
    let visit = SingleThreadedBreadthFirstVisit::with_start(&graph, &factory, 10000);
    visit.visit(Option::<ProgressLogger>::None).unwrap()
}

#[cfg_attr(windows, allow(dead_code))]
fn test_bfv_cnr_2000_parallel_exclusive() -> Vec<usize> {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .unwrap();
    let factory = Factory {};
    let visit = ParallelExclusiveBreadthFirstVisit::with_start(&graph, &factory, 10000);
    visit.visit(Option::<ProgressLogger>::None).unwrap()
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
    test_bfv_cnr_2000_parallel_exclusive
);
