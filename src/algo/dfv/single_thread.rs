use crate::prelude::*;
use sux::bits::BitVec;
use webgraph::traits::{RandomAccessGraph, RandomAccessLabeling};

/// A sequential depth-first visit.
///
/// In case the callback returns `false`, the visit behaves as follows:
/// * If the event is [`Event::Unknown`], the node will be marked as discovered
///   but ignored.
/// * If the event is [`Event::Known`], the successor enumeration will be
///   interrupted.
/// * If the event is [`Event::Completed`], the visit will be terminated.
pub struct SingleThreadedDepthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    /// Entries on this stack represent the iterator on the successors of a node
    /// and the parent of the node. This approach makes it possible to avoid
    /// storing both the current and the parent node in the stack.
    stack: Vec<(
        <<G as RandomAccessLabeling>::Labels<'a> as IntoIterator>::IntoIter,
        usize,
    )>,
    discovered: BitVec,
}

impl<'a, G: RandomAccessGraph> SingleThreadedDepthFirstVisit<'a, G> {
    /// Creates a new sequential visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> Self {
        Self {
            graph,
            stack: Vec::with_capacity(16),
            discovered: BitVec::new(graph.num_nodes()),
        }
    }
}

impl<'a, G: RandomAccessGraph> DepthFirstVisit for SingleThreadedDepthFirstVisit<'a, G> {
    fn visit_from_node(
        &mut self,
        callback: impl Fn(DFVArgs) -> bool + Sync,
        visit_root: usize,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) {
        if self.discovered[visit_root] {
            return;
        }

        // This variable keeps track of the current node being visited; the
        // parent node is derived at each iteration of the 'recurse loop.
        let mut current_node = visit_root;

        let args = DFVArgs {
            node: visit_root,
            pred: visit_root,
            root: visit_root,
            distance: 0,
            event: Event::Unknown,
        };

        if !callback(args) {
            return;
        }

        self.discovered.set(current_node, true);
        self.stack
            .push((self.graph.successors(visit_root).into_iter(), visit_root));

        'recurse: loop {
            let depth = self.stack.len();
            let Some((iter, parent)) = self.stack.last_mut() else {
                break;
            };
            let parent_node = *parent;

            for succ in iter.by_ref() {
                // Check if node should be visited
                if self.discovered[succ] {
                    // Node has already been visited
                    if !callback(DFVArgs {
                        node: succ,
                        pred: current_node,
                        root: visit_root,
                        distance: depth + 1,
                        event: Event::Known,
                    }) {
                        break;
                    }
                } else {
                    // First time seeing node
                    if callback(DFVArgs {
                        node: succ,
                        pred: current_node,
                        root: visit_root,
                        distance: depth + 1,
                        event: Event::Unknown,
                    }) {
                        self.discovered.set(succ, true);
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
            if !callback(DFVArgs {
                node: current_node,
                pred: parent_node,
                root: visit_root,
                distance: depth,
                event: Event::Completed,
            }) {
                break;
            }

            // We're going up one stack level, so the next current_node
            // is the current parent.
            current_node = parent_node;
            self.stack.pop();

            pl.light_update();
        }
    }

    fn visit(
        &mut self,
        callback: impl Fn(DFVArgs) -> bool + Sync,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) {
        for node in 0..self.graph.num_nodes() {
            self.visit_from_node(&callback, node, pl);
        }
    }

    #[inline(always)]
    fn reset(&mut self) {
        self.stack.clear();
        self.discovered.fill(false);
    }
}
