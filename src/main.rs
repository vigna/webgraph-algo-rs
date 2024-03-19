use anyhow::Result;
use dsi_progress_logger::{ProgressLog, ProgressLogger};
use webgraph::graphs::BVGraph;
use webgraph::traits::RandomAccessGraph;
use webgraph_algo::algo::bfv::SingleThreadedBreadthFirstVisit;
use webgraph_algo::algo::GraphVisit;
use webgraph_algo::{NodeFactory, NodeVisit};

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
    type PartialResult = f64;

    #[inline]
    fn visit(self, partial_result: f64) -> Self::PartialResult {
        partial_result + self.index as f64 / self.graph.num_nodes() as f64
    }

    fn init_result() -> Self::PartialResult {
        0.0
    }
}

fn main() -> Result<()> {
    stderrlog::new().verbosity(2).init()?;
    let graph = BVGraph::with_basename("graphs/sk-2005").load()?;
    let node_factory = Factory::new(&graph);
    let visit = SingleThreadedBreadthFirstVisit::new(&graph, &node_factory);
    let mut pl = ProgressLogger::default();
    pl.display_memory(true).local_speed(true);
    let result = visit.visit(&mut pl);
    pl.info(format_args!("Average node index: {}", result));
    Ok(())
}
