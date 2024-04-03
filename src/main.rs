use anyhow::Result;
use dsi_progress_logger::{ProgressLog, ProgressLogger};
use webgraph::graphs::BVGraph;
use webgraph::traits::{RandomAccessGraph, SequentialLabeling};
use webgraph_algo::algo::bfv::*;
use webgraph_algo::prelude::*;

struct Node<'a, G: RandomAccessGraph> {
    graph: &'a G,
    index: usize,
}

struct Factory<'a, G: RandomAccessGraph> {
    graph: &'a G,
}

impl<'a, G: RandomAccessGraph> Factory<'a, G> {
    fn new(graph: &G) -> Factory<G> {
        Factory { graph }
    }
}

impl<'a, G: RandomAccessGraph> NodeFactory for Factory<'a, G> {
    type Node = Node<'a, G>;
    #[inline]
    fn node_from_index(&self, node_index: usize) -> Self::Node {
        Node {
            index: node_index,
            graph: self.graph,
        }
    }
}

impl<'a, G: RandomAccessGraph> NodeVisit for Node<'a, G> {
    type AccumulatedResult = Vec<usize>;
    type VisitResult = usize;

    #[inline]
    fn visit(self) -> Self::VisitResult {
        self.graph.successors(self.index);
        self.index
    }

    fn accumulate_result(
        partial_result: &mut Self::AccumulatedResult,
        visit_result: Self::VisitResult,
    ) {
        partial_result.push(visit_result)
    }

    fn init_result() -> Self::AccumulatedResult {
        Vec::new()
    }
}

impl<'a, G: RandomAccessGraph> AssociativeNodeVisit for Node<'a, G> {
    fn merge_result(
        accumulated_result: &mut Self::AccumulatedResult,
        mut partial_result: Self::AccumulatedResult,
    ) {
        accumulated_result.append(&mut partial_result)
    }
}

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
    let node_factory = Factory::new(&graph);

    let parallel_exclusive_visit =
        ParallelExclusiveBreadthFirstVisit::with_start(&graph, &node_factory, start);
    let mut parallel_exclusive_pl = ProgressLogger::default();
    parallel_exclusive_pl.display_memory(true).local_speed(true);
    let mut par_exclusive_result = parallel_exclusive_visit.visit(parallel_exclusive_pl)?;
    main_pl.info(format_args!("Sorting parallel exclusive result"));
    par_exclusive_result.sort();

    let parallel_associative_visit =
        ParallelAssociativeBreadthFirstVisit::with_start(&graph, &node_factory, start);
    let mut parallel_associative_pl = ProgressLogger::default();
    parallel_associative_pl
        .display_memory(true)
        .local_speed(true);
    let mut par_associative_result = parallel_associative_visit.visit(parallel_associative_pl)?;
    main_pl.info(format_args!("Sorting parallel associative"));
    par_associative_result.sort();

    let sequential_visit =
        SingleThreadedBreadthFirstVisit::with_start(&graph, &node_factory, start);
    let mut sequential_pl = ProgressLogger::default();
    sequential_pl.display_memory(true).local_speed(true);
    let mut sequential_result = sequential_visit.visit(sequential_pl)?;
    main_pl.info(format_args!("Sorting sequential result"));
    sequential_result.sort();

    assert!(sequential_result == par_exclusive_result);
    assert!(sequential_result == par_associative_result);
    assert!(par_exclusive_result == par_associative_result);
    assert_eq!(sequential_result.len(), graph.num_nodes());
    assert_eq!(par_associative_result.len(), graph.num_nodes());
    assert_eq!(par_exclusive_result.len(), graph.num_nodes());

    Ok(())
}
