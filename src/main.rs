use anyhow::Result;
use dsi_progress_logger::{ProgressLog, ProgressLogger};
use webgraph::graphs::BVGraph;
use webgraph::traits::RandomAccessGraph;
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

fn main() -> Result<()> {
    stderrlog::new().verbosity(2).init()?;
    let graph = BVGraph::with_basename("graphs/cnr-2000").load()?;
    let main_pl = ProgressLogger::default();
    let node_factory = Factory::new(&graph);

    let pram_visit = ParallelExclusiveBreadthFirstVisit::new(&graph, &node_factory);
    let mut pram_pl = ProgressLogger::default();
    pram_pl.display_memory(true).local_speed(true);
    let mut pram_result = pram_visit.visit(pram_pl)?;
    main_pl.info(format_args!("Sorting parallel result"));
    pram_result.sort();

    let sequential_visit = SingleThreadedBreadthFirstVisit::new(&graph, &node_factory);
    let mut sequential_pl = ProgressLogger::default();
    sequential_pl.display_memory(true).local_speed(true);
    let mut sequential_result = sequential_visit.visit(sequential_pl)?;
    main_pl.info(format_args!("Sorting sequential result"));
    sequential_result.sort();

    assert!(sequential_result == pram_result);

    Ok(())
}
