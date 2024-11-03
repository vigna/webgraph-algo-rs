use crate::algo::visits::{
    dfv::{Args, Event},
    SeqVisit,
};
use sux::bits::BitVec;
use webgraph::traits::{RandomAccessGraph, RandomAccessLabeling};

/// A sequential depth-first visit.
///
/// In case the filter returns `false`, the visit behaves as follows:
/// * If the event is [`Event::Unknown`], the node will be not marked as discovered
///   and ignored.
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
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            stack: Vec::with_capacity(16),
            discovered: BitVec::new(num_nodes),
        }
    }
}

impl<'a, G: RandomAccessGraph> SeqVisit<Args> for SingleThreadedDepthFirstVisit<'a, G> {
    fn visit_from_node<C: FnMut(Args), F: Fn(&Args) -> bool>(
        &mut self,
        root: usize,
        mut callback: C,
        filter: F,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) {
        if self.discovered[root] {
            return;
        }

        // This variable keeps track of the current node being visited; the
        // parent node is derived at each iteration of the 'recurse loop.
        let mut current_node = root;

        let args = Args {
            node: root,
            pred: root,
            root,
            depth: 0,
            event: Event::Unknown,
        };

        if !filter(&args) {
            return;
        }

        callback(args);

        self.discovered.set(current_node, true);
        self.stack
            .push((self.graph.successors(root).into_iter(), root));

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
                    let args = Args {
                        node: succ,
                        pred: current_node,
                        root,
                        depth: depth + 1,
                        event: Event::Known,
                    };
                    if !filter(&args) {
                        break;
                    }
                    callback(args);
                } else {
                    // First time seeing node
                    let args = Args {
                        node: succ,
                        pred: current_node,
                        root,
                        depth: depth + 1,
                        event: Event::Unknown,
                    };
                    if filter(&args) {
                        callback(args);
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

            let args = Args {
                node: current_node,
                pred: parent_node,
                root,
                depth,
                event: Event::Completed,
            };
            if !filter(&args) {
                break;
            }
            callback(args);

            // We're going up one stack level, so the next current_node
            // is the current parent.
            current_node = parent_node;
            self.stack.pop();

            pl.light_update();
        }
    }

    fn visit<C: FnMut(Args), F: Fn(&Args) -> bool>(
        &mut self,
        mut callback: C,
        filter: F,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) {
        for node in 0..self.graph.num_nodes() {
            self.visit_from_node(node, &mut callback, &filter, pl);
        }
    }

    fn reset(&mut self) {
        self.stack.clear();
        self.discovered.fill(false);
    }
}
