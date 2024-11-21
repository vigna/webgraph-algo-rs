use crate::algo::visits::{depth_first::*, Sequential, StoppedWhenDone};
use dsi_progress_logger::ProgressLog;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

use super::BasicSccs;

/// Tarjan's algorithm for strongly connected components.
pub fn tarjan(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> BasicSccs {
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Computing strongly connected components...");

    let mut visit = SeqPred::new(&graph);
    let mut lead = BitVec::with_capacity(128);
    // Sentinel value guaranteeing that this stack is never empty
    lead.push(true);
    let mut component_stack = Vec::with_capacity(16);
    let mut high_link = vec![0; num_nodes].into_boxed_slice();
    // Node timestamps will start at num_nodes and will decrease with time,
    // that is, they will go in opposite order with respect to the classical
    // implementation. We keep track of the highest index seen, instead
    // of the lowest index seen, and we number compoments starting from
    // zero. We also raise index by the number of elements of each emitted
    // component. In this way unvisited nodes and emitted nodes have always
    // a lower value than index. This strategy is analogous to that
    // described in https://www.timl.id.au/scc, but in that case using
    // increasing timestamps results in components not being labelled
    // starting from zero, which is the case here instead.
    let mut index = num_nodes;
    let mut root_low_link = 0;
    let mut number_of_components = 0;

    if visit
        .visit_all(
            |event| {
                match event {
                    EventPred::Init { .. } => {
                        root_low_link = index;
                    }
                    EventPred::Previsit { curr, .. } => {
                        high_link[curr] = index; // >= num_nodes, <= umax::SIZE
                        index -= 1;
                        lead.push(true);
                    }
                    EventPred::Revisit { curr, pred, .. } => {
                        // curr has not been emitted yet but it has a higher link
                        if high_link[pred] < high_link[curr] {
                            // Safe as the stack is never empty
                            lead.set(lead.len() - 1, false);
                            high_link[pred] = high_link[curr];
                            if high_link[pred] == root_low_link && index == 0 {
                                // All nodes have been discovered, and we
                                // found a high link identical to that of the
                                // root: thus, all nodes on the visit path
                                // and all nodes in the component stack
                                // belong to the same component.

                                // pred is the last node on the visit path,
                                // so it won't be returned by the stack method
                                high_link[pred] = number_of_components;
                                for &node in component_stack.iter() {
                                    high_link[node] = number_of_components;
                                }
                                // Nodes on the visit path will be assigned
                                // to the same component later
                                return Err(StoppedWhenDone {});
                            }
                        }
                    }
                    EventPred::Postvisit { curr, pred, .. } => {
                        // Safe as the stack is never empty
                        if lead.pop().unwrap() {
                            // Set the component index of nodes in the component
                            // stack with higher link than the current node
                            while let Some(node) = component_stack.pop() {
                                // TODO: ugly
                                if high_link[curr] < high_link[node] {
                                    component_stack.push(node);
                                    break;
                                }
                                index += 1;
                                high_link[node] = number_of_components;
                            }
                            // Set the component index of the current node
                            high_link[curr] = number_of_components;
                            index += 1;
                            number_of_components += 1;
                        } else {
                            component_stack.push(curr);
                            // Propagate knowledge to the parent
                            if high_link[pred] < high_link[curr] {
                                // Safe as the stack is never empty
                                lead.set(lead.len() - 1, false);
                                high_link[pred] = high_link[curr];
                            }
                        }
                    }
                    _ => {}
                }
                Ok(())
            },
            pl,
        )
        .is_err()
    {
        // In case we exited early, complete the assignment
        for node in visit.stack() {
            high_link[node] = number_of_components;
        }
        number_of_components += 1;
    }
    pl.done();
    BasicSccs::new(number_of_components, high_link)
}
