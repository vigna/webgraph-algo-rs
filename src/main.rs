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
    type AccumulatedResult = f64;
    type VisitResult = f64;

    #[inline]
    fn visit(self) -> Self::VisitResult {
        self.index as f64 / self.graph.num_nodes() as f64
    }

    fn accumulate_result(
        partial_result: Self::AccumulatedResult,
        visit_result: Self::VisitResult,
    ) -> Self::AccumulatedResult {
        partial_result + visit_result
    }

    fn init_result() -> Self::AccumulatedResult {
        0.0
    }
}

fn main() -> Result<()> {
    stderrlog::new().verbosity(2).init()?;
    let graph = BVGraph::with_basename("graphs/sk-2005").load()?;
    let main_pl = ProgressLogger::default();
    let node_factory = Factory::new(&graph);

    let pram_visit = PramBreadthFirstVisit::new(&graph, &node_factory);
    let mut pram_pl = ProgressLogger::default();
    pram_pl.display_memory(true).local_speed(true);
    let pram_result = pram_visit.visit(pram_pl)?;
    main_pl.info(format_args!("Average node index: {}", pram_result));

    let sequential_visit = SingleThreadedBreadthFirstVisit::new(&graph, &node_factory);
    let mut sequential_pl = ProgressLogger::default();
    sequential_pl.display_memory(true).local_speed(true);
    let sequential_result = sequential_visit.visit(sequential_pl)?;
    main_pl.info(format_args!("Average node index: {}", sequential_result));

    Ok(())
}
