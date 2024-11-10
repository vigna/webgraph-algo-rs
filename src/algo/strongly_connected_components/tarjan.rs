use super::traits::StronglyConnectedComponents;
use crate::algo::visits::{depth_first::*, Sequential, StoppedWhenDone};
use dsi_progress_logger::ProgressLog;

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

    fn compute(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Self {
        let mut visit = Tarjan::new(graph);

        visit.run(pl);

        TarjanStronglyConnectedComponents {
            component: visit.component,
            n_of_components: visit.number_of_components,
        }
    }
}

struct Tarjan<G: RandomAccessGraph> {
    graph: G,
    pub component: Vec<usize>,
    pub number_of_components: usize,
}

impl<G: RandomAccessGraph> Tarjan<G> {
    fn new(graph: G) -> Tarjan<G> {
        let num_nodes = graph.num_nodes();
        Tarjan {
            graph,
            component: vec![0; num_nodes],
            number_of_components: 0,
        }
    }

    fn run(&mut self, pl: &mut impl ProgressLog) {
        let mut visit = SeqPath::new(&self.graph);
        let num_nodes = self.graph.num_nodes();
        pl.item_name("node");
        pl.expected_updates(Some(num_nodes));
        pl.start("Computing strongly connected components");
        let mut lead = Vec::with_capacity(16);
        // Sentinel value guaranteeing that this stack is never empty
        lead.push(true);
        let mut component_stack = Vec::with_capacity(16);
        let low_link = &mut self.component;
        let mut current_index = 0;
        let mut root_low_link = 0;

        if visit
            .visit_all(
                |args| {
                    match args {
                        EventPred::Init { .. } => {
                            root_low_link = current_index;
                        }
                        EventPred::Previsit { curr, .. } => {
                            low_link[curr] = current_index;
                            current_index += 1;
                            lead.push(true);
                        }
                        EventPred::Revisit {
                            on_stack: true,
                            curr,
                            pred,
                            ..
                        } => {
                            if low_link[curr] < low_link[pred] {
                                // Safe as the stack is never empty
                                *lead.last_mut().unwrap() = false;
                                low_link[pred] = low_link[curr];

                                /*if low_link[pred] == root_low_link && current_index == num_nodes {
                                    // All nodes have been discovered, and we
                                    // found a low link identical to that of the
                                    // root: thus, the current node, all nodes
                                    // on the visit path and all nodes in the
                                    // component stack belong to the same
                                    // component.

                                    low_link[curr] = self.number_of_components;
                                    for &node in component_stack.iter() {
                                        low_link[node] = self.number_of_components;
                                    }
                                    // Nodes on the visit path will be assigned
                                    // to the same component later
                                    return Err(StoppedWhenDone {});
                                }*/
                            }
                        }
                        EventPred::Postvisit { curr, pred, .. } => {
                            // Safe as the stack is never empty
                            if lead.pop().unwrap() {
                                debug_assert!(low_link[curr] >= low_link[pred]);
                                // Set the component index of nodes in the component
                                // stack with lower low link than the current node
                                while let Some(node) = component_stack.pop() {
                                    // TODO: ugly
                                    if low_link[node] < low_link[curr] {
                                        component_stack.push(node);
                                        break;
                                    }
                                    low_link[node] = self.number_of_components;
                                }
                                // Set the component index of the current node
                                low_link[curr] = self.number_of_components;
                                self.number_of_components += 1;
                            } else {
                                component_stack.push(curr);
                                // Propagate knowledge to the parent
                                if low_link[curr] < low_link[pred] {
                                    // Safe as the stack is never empty
                                    *lead.last_mut().unwrap() = false;
                                    low_link[pred] = low_link[curr];
                                }
                            }
                        }
                        _ => (),
                    }
                    Ok::<_, StoppedWhenDone>(())
                },
                pl,
            )
            .is_err()
        {
            // In case we exited early, complete the assignment
            for node in visit.stack() {
                self.component[node] = self.number_of_components;
            }
            self.number_of_components += 1;
        }
        pl.done();
    }
}
