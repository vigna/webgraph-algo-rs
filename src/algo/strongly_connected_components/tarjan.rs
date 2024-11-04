use super::traits::StronglyConnectedComponents;
use crate::{algo::visits::dfv::*, algo::visits::SeqVisit};
use common_traits::NonZero;
use dsi_progress_logger::ProgressLog;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// Implementation of Tarjan's algorithm to compute the strongly connected components
/// on a graph.
pub struct TarjanStronglyConnectedComponents {
    n_of_components: usize,
    component: Vec<usize>,
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
        None
    }

    fn compute(
        graph: impl RandomAccessGraph,
        compute_buckets: bool,
        pl: &mut impl ProgressLog,
    ) -> Self {
        let mut visit = Tarjan::new(graph, compute_buckets);

        visit.run(pl.clone());

        TarjanStronglyConnectedComponents {
            component: visit.components,
            n_of_components: visit.number_of_components,
        }
    }
}

struct Tarjan<G: RandomAccessGraph> {
    graph: G,
    pub components: Vec<usize>,
    pub number_of_components: usize,
}

impl<G: RandomAccessGraph> Tarjan<G> {
    fn new(graph: G, compute_buckets: bool) -> Tarjan<G> {
        let num_nodes = graph.num_nodes();
        Tarjan {
            graph,
            components: vec![0; num_nodes],
            number_of_components: 0,
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
        let mut smaller_seen = Vec::with_capacity(16);
        // Sentinel value guaranteeing that this stack is never empty
        smaller_seen.push(false);
        let mut current_index = 0;
        let mut component_stack = Vec::with_capacity(16);

        visit
            .visit(
                |&Args {
                     node,
                     pred,
                     root: _root,
                     depth: _depth,
                     event,
                 }| {
                    match event {
                        Event::Unknown => {
                            self.components[node] = current_index;
                            current_index += 1;
                            smaller_seen.push(false);
                            component_stack.push(node);
                        }
                        Event::Known(true) => {
                            // This test is necessary for loops
                            if self.components[node] < self.components[pred] {
                                // Safe as the stack is never empty
                                *smaller_seen.last_mut().unwrap() = true;
                                self.components[pred] = self.components[node];
                            }
                        }
                        Event::Completed => {
                            // Safe as the stack is never empty
                            if smaller_seen.pop().unwrap() {
                                if self.components[node] < self.components[pred] {
                                    // Safe as the stack is never empty
                                    *smaller_seen.last_mut().unwrap() = true;
                                    self.components[pred] = self.components[node];
                                }
                            } else {
                                while let Some(v) = component_stack.pop() {
                                    self.components[v] = self.number_of_components;
                                    if v == node {
                                        break;
                                    }
                                }
                                self.number_of_components += 1;
                            }
                        }
                        _ => {}
                    }
                    Ok(())
                },
                |_| true,
                &mut pl,
            )
            .unwrap(); // Safe as infallible

        pl.done();
    }
}
