use crate::prelude::*;
use anyhow::Result;
use sux::bits::BitVec;
use webgraph::traits::{RandomAccessGraph, RandomAccessLabeling};

/// A simple sequential Depth First visit on a graph.
pub struct SingleThreadedDepthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    /// Entries on this stack represent the iterator on the successors of a node
    /// and the parent of the node. This approach makes it possible to avoid
    /// storing both the current and the parent node in the stack.
    stack: Vec<(
        <<G as RandomAccessLabeling>::Labels<'a> as IntoIterator>::IntoIter,
        usize,
    )>,
    visited: BitVec,
}

impl<'a, G: RandomAccessGraph> SingleThreadedDepthFirstVisit<'a, G> {
    /// Creates a new sequential visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> Self {
        Self {
            graph,
            stack: Vec::new(),
            visited: BitVec::new(graph.num_nodes()),
        }
    }
}

impl<'a, G: RandomAccessGraph> DepthFirstGraphVisit for SingleThreadedDepthFirstVisit<'a, G> {
    fn visit_from_node_filtered<
        C: Fn(DFVArgs, DepthFirstVisitEvent) + Sync,
        F: Fn(DFVArgs) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        visit_root: usize,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Result<()> {
        if self.visited[visit_root] {
            return Ok(());
        }

        // This variable keeps track of the current node being visited; the
        // parent node is derived at each iteration of the 'recurse loop.
        let mut current_node = visit_root;

        callback(
            DFVArgs {
                node_index: visit_root,
                parent: visit_root,
                root: visit_root,
                distance_from_root: 0,
            },
            DepthFirstVisitEvent::Discover,
        );

        self.visited.set(current_node, true);
        self.stack
            .push((self.graph.successors(visit_root).into_iter(), visit_root));

        'recurse: loop {
            let depth = self.stack.len();
            let Some((iter, parent)) = self.stack.last_mut() else {
                break;
            };
            let parent_node = *parent;

            for succ in iter.by_ref() {
                let args = DFVArgs {
                    node_index: succ,
                    parent: current_node,
                    root: visit_root,
                    distance_from_root: depth + 1,
                };
                // Check if node should be visited
                if filter(args) {
                    if self.visited[succ] {
                        // Node has already been visited
                        callback(args, DepthFirstVisitEvent::AlreadyVisited);
                    } else {
                        // First time seeing node
                        callback(args, DepthFirstVisitEvent::Discover);

                        self.visited.set(succ, true);
                        // current_node is the parent of succ
                        self.stack
                            .push((self.graph.successors(succ).into_iter(), current_node));
                        // At the next iteration, succ will be the current node
                        current_node = succ;
                        continue 'recurse;
                    }
                }
            }

            // Emit node
            callback(
                DFVArgs {
                    node_index: current_node,
                    parent: parent_node,
                    root: visit_root,
                    distance_from_root: depth,
                },
                DepthFirstVisitEvent::Emit,
            );

            // We're going up one stack level, so the next current_node
            // is the current parent.
            current_node = parent_node;
            self.stack.pop();

            pl.light_update();
        }

        Ok(())
    }

    #[inline(always)]
    fn reset(&mut self) -> Result<()> {
        self.stack.clear();
        self.visited.fill(false);
        Ok(())
    }
}
