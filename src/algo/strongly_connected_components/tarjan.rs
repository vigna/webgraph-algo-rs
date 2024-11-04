use super::traits::StronglyConnectedComponents;
use crate::{algo::visits::dfv::*, algo::visits::SeqVisit};
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// Implementation of Tarjan's algorithm to compute the strongly connected components
/// on a graph.
pub struct TarjanStronglyConnectedComponents {
    n_of_components: usize,
    component: Vec<usize>,
    buckets: Option<BitVec>,
}

impl StronglyConnectedComponents for TarjanStronglyConnectedComponents {
    fn number_of_components(&self) -> usize {
        self.n_of_components
    }

    fn component(&self) -> &[usize] {
        self.component.as_ref()
    }

    fn component_mut(&mut self) -> &mut [usize] {
        self.component.as_mut()
    }

    fn buckets(&self) -> Option<&BitVec> {
        match &self.buckets {
            Some(b) => Some(b),
            None => None,
        }
    }

    fn compute(
        graph: impl RandomAccessGraph,
        compute_buckets: bool,
        pl: &mut impl ProgressLog,
    ) -> Self {
        let mut visit = Tarjan::new(graph, compute_buckets);

        visit.run(pl.clone());

        TarjanStronglyConnectedComponents {
            buckets: visit.buckets,
            component: visit.components,
            n_of_components: visit.number_of_components,
        }
    }
}

struct Tarjan<G: RandomAccessGraph> {
    graph: G,
    pub components: Vec<usize>,
    pub buckets: Option<BitVec>,
    indexes: Vec<Option<NonMaxUsize>>,
    lowlinks: Vec<usize>,
    terminal: Option<BitVec>,
    /// The first-Tarjan clock (incremented at each Tarjaned node).
    current_index: usize,
    pub number_of_components: usize,
    stack: Vec<usize>,
}

impl<G: RandomAccessGraph> Tarjan<G> {
    fn new(graph: G, compute_buckets: bool) -> Tarjan<G> {
        let num_nodes = graph.num_nodes();
        Tarjan {
            graph,
            buckets: if compute_buckets {
                Some(BitVec::new(num_nodes))
            } else {
                None
            },
            terminal: if compute_buckets {
                Some(BitVec::with_value(num_nodes, true))
            } else {
                None
            },
            current_index: 0,
            indexes: vec![None; num_nodes],
            lowlinks: vec![usize::MAX; num_nodes],
            number_of_components: 0,
            components: vec![0; num_nodes],
            stack: Vec::new(),
        }
    }

    fn run(&mut self, mut pl: impl ProgressLog) {
        let mut visit =
            SingleThreadedDepthFirstVisit::<ThreeState, std::convert::Infallible, _>::new(
                &self.graph,
            );
        pl.item_name("node");
        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Computing strongly connected components");

        visit.visit(
            |&Args {
                 node,
                 pred,
                 root: _root,
                 depth: _depth,
                 event,
             }| {
                match event {
                    Event::Unknown => {
                        self.indexes[node] = Some(
                            NonMaxUsize::new(self.current_index)
                                .expect("indexes should not exceed usize::MAX"),
                        );
                        self.lowlinks[node] = self.current_index;
                        self.current_index += 1;
                        self.stack.push(node);
                    }
                    Event::Known(on_stack) => {
                        if on_stack {
                            // TODO
                            self.lowlinks[pred] = std::cmp::min(
                                self.lowlinks[pred],
                                self.indexes[node].unwrap().into(),
                            );
                        } else if let Some(t) = &mut self.terminal {
                            t.set(pred, false);
                        }
                    }
                    Event::Completed => {
                        if self.lowlinks[node] == self.indexes[node].unwrap().into() {
                            if let Some(b) = &mut self.buckets {
                                let t = self.terminal.as_mut().unwrap();
                                let terminal = t[node];
                                while let Some(v) = self.stack.pop() {
                                    self.components[v] = self.number_of_components;
                                    t.set(v, false);
                                    if terminal && self.graph.outdegree(v) != 0 {
                                        b.set(v, true);
                                    }
                                    if v == node {
                                        break;
                                    }
                                }
                            } else {
                                while let Some(v) = self.stack.pop() {
                                    self.components[v] = self.number_of_components;
                                    if v == node {
                                        break;
                                    }
                                }
                            }
                            self.number_of_components += 1;
                        }

                        if node != pred {
                            self.lowlinks[pred] =
                                std::cmp::min(self.lowlinks[pred], self.lowlinks[node]);
                            if let Some(t) = &mut self.terminal {
                                if !t[node] {
                                    t.set(pred, false);
                                }
                            }
                        }
                    }
                }
                Ok(())
            },
            |_| true,
            &mut pl,
        );

        pl.done();
    }
}
