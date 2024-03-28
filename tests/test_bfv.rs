use std::iter::zip;

use anyhow::{Context, Ok, Result};
use dsi_progress_logger::ProgressLogger;
use sux::bits::BitVec;
use webgraph::graphs::BVGraph;
use webgraph::traits::RandomAccessGraph;
use webgraph_algo::algo::bfv::*;
use webgraph_algo::prelude::*;

struct Node {
    index: usize,
}

struct Factory {}

impl NodeVisit for Node {
    type VisitResult = usize;
    type AccumulatedResult = Vec<usize>;

    fn init_result() -> Self::AccumulatedResult {
        Vec::new()
    }

    fn accumulate_result(
        partial_result: &mut Self::AccumulatedResult,
        visit_result: Self::VisitResult,
    ) {
        partial_result.push(visit_result)
    }

    fn visit(self) -> Self::VisitResult {
        self.index
    }
}

impl NodeFactory for Factory {
    type Node = Node;

    fn node_from_index(&self, node_index: usize) -> Self::Node {
        Node { index: node_index }
    }
}

fn get_correct_bfv_order<G: RandomAccessGraph>(graph: &G, start: usize) -> Vec<Vec<usize>> {
    let mut distances = Vec::new();
    let mut visited = BitVec::new(graph.num_nodes());
    let mut queue = Vec::new();

    visited.set(start, true);
    queue.push(start);

    loop {
        if queue.is_empty() {
            break;
        }
        let mut nodes = Vec::new();
        nodes.append(&mut queue);
        for node in nodes.clone() {
            for succ in graph.successors(node) {
                if !visited[succ] {
                    visited.set(succ, true);
                    queue.push(succ);
                }
            }
        }
        nodes.sort();
        distances.push(nodes);
    }

    let mut remainder = Vec::new();

    for index in 0..graph.num_nodes() {
        if !visited[index] {
            remainder.push(index);
        }
    }

    if !remainder.is_empty() {
        distances.push(remainder);
    }

    distances
}

#[test]
fn test_sequential_bfv() -> Result<()> {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .with_context(|| "Cannot load graph")?;
    let factory = Factory {};
    let visit = SingleThreadedBreadthFirstVisit::new(&graph, &factory);

    let result = visit
        .visit(Option::<ProgressLogger>::None)
        .with_context(|| "Error during visit")?;

    let expected_distances = get_correct_bfv_order(&graph, 0);

    let mut distances = Vec::new();
    let mut count = 0;
    for distance in expected_distances.clone() {
        let mut nodes = result[count..count + distance.len()].to_owned();
        nodes.sort();
        distances.push(nodes);
        count += distance.len();
    }

    assert_eq!(distances.len(), expected_distances.len());
    for (distance, expected_distance) in zip(distances, expected_distances) {
        assert_eq!(distance, expected_distance);
    }

    Ok(())
}

#[test]
fn test_sequential_bfv_with_start() -> Result<()> {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .with_context(|| "Cannot load graph")?;
    let factory = Factory {};
    let visit = SingleThreadedBreadthFirstVisit::with_start(&graph, &factory, 10000);

    let result = visit
        .visit(Option::<ProgressLogger>::None)
        .with_context(|| "Error during visit")?;

    let expected_distances = get_correct_bfv_order(&graph, 10000);

    let mut distances = Vec::new();
    let mut count = 0;
    for distance in expected_distances.clone() {
        let mut nodes = result[count..count + distance.len()].to_owned();
        nodes.sort();
        distances.push(nodes);
        count += distance.len();
    }

    assert_eq!(distances.len(), expected_distances.len());
    for (distance, expected_distance) in zip(distances, expected_distances) {
        assert_eq!(distance, expected_distance);
    }

    Ok(())
}

#[test]
fn test_parallel_bfv() -> Result<()> {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .with_context(|| "Cannot load graph")?;
    let factory = Factory {};
    let visit = ParallelExclusiveBreadthFirstVisit::new(&graph, &factory);

    let result = visit
        .visit(Option::<ProgressLogger>::None)
        .with_context(|| "Error during visit")?;

    let expected_distances = get_correct_bfv_order(&graph, 0);

    let mut distances = Vec::new();
    let mut count = 0;
    for distance in expected_distances.clone() {
        let mut nodes = result[count..count + distance.len()].to_owned();
        nodes.sort();
        distances.push(nodes);
        count += distance.len();
    }

    assert_eq!(distances.len(), expected_distances.len());
    for (distance, expected_distance) in zip(distances, expected_distances) {
        assert_eq!(distance, expected_distance);
    }

    Ok(())
}

#[test]
fn test_parallel_bfv_with_start() -> Result<()> {
    let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
        .load()
        .with_context(|| "Cannot load graph")?;
    let factory = Factory {};
    let visit = ParallelExclusiveBreadthFirstVisit::with_start(&graph, &factory, 10000);

    let result = visit
        .visit(Option::<ProgressLogger>::None)
        .with_context(|| "Error during visit")?;

    let expected_distances = get_correct_bfv_order(&graph, 10000);

    let mut distances = Vec::new();
    let mut count = 0;
    for distance in expected_distances.clone() {
        let mut nodes = result[count..count + distance.len()].to_owned();
        nodes.sort();
        distances.push(nodes);
        count += distance.len();
    }

    assert_eq!(distances.len(), expected_distances.len());
    for (distance, expected_distance) in zip(distances, expected_distances) {
        assert_eq!(distance, expected_distance);
    }

    Ok(())
}
