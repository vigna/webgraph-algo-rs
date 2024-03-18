use anyhow::Result;
use dsi_progress_logger::{ProgressLog, ProgressLogger};
use webgraph::graphs::BVGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::SingleThreadedBreadthFirstVisit;
use webgraph_algo::{NodeFactory, NodeVisit};

struct Node {
    index: usize,
}

struct Factory {}

impl Factory {
    fn new() -> Factory {
        Factory {}
    }
}

impl NodeFactory for Factory {
    type Node = Node;
    fn node_from_index(&self, node_index: usize) -> Self::Node {
        Node { index: node_index }
    }
}

impl NodeVisit for Node {
    type VisitReturn = usize;

    fn visit(self) -> Self::VisitReturn {
        self.index
    }
}

fn main() -> Result<()> {
    stderrlog::new().verbosity(2).init()?;
    let graph = BVGraph::with_basename("graphs/sk-2005").load()?;
    let node_factory = Factory::new();
    let visit = SingleThreadedBreadthFirstVisit::new(&graph, &node_factory);
    let mut pl = ProgressLogger::default();
    pl.item_name("node")
        .display_memory(true)
        .local_speed(true)
        .expected_updates(Some(graph.num_nodes()));
    pl.start("Visiting graph in BFS order...");
    for node in visit {
        pl.light_update();
        node.visit();
    }
    pl.stop();
    pl.done();
    Ok(())
}
