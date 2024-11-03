use crate::algo::visits::{
    dfv::{Args, Event},
    SeqVisit,
};
use sux::bits::BitVec;
use sux::traits::BitFieldSliceMut;
use webgraph::traits::{RandomAccessGraph, RandomAccessLabeling};

/// A sequential depth-first visit.
///
/// In case the filter returns `false`, the visit behaves as follows:
/// * If the event is [`Event::Unknown`], the node will be marked as discovered
///   but ignored.
/// * If the event is [`Event::Known`], the visit will be interrupted.
pub struct SingleThreadedDepthFirstVisit<'a, S: NodeState, G: RandomAccessGraph> {
    graph: &'a G,
    /// Entries on this stack represent the iterator on the successors of a node
    /// and the parent of the node. This approach makes it possible to avoid
    /// storing both the current and the parent node in the stack.
    stack: Vec<(
        <<G as RandomAccessLabeling>::Labels<'a> as IntoIterator>::IntoIter,
        usize,
    )>,
    state: S,
}

impl<'a, G: RandomAccessGraph> SingleThreadedDepthFirstVisit<'a, ThreeState, G> {
    /// Creates a new sequential visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> Self {
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            stack: Vec::with_capacity(16),
            state: ThreeState::new(num_nodes),
        }
    }
}

impl<'a, G: RandomAccessGraph> SingleThreadedDepthFirstVisit<'a, TwoState, G> {
    /// Creates a new sequential visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> Self {
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            stack: Vec::with_capacity(16),
            state: TwoState::new(num_nodes),
        }
    }
}

/// A two-state implementation of [`NodeState`].
///
/// This implementation does not keep track of nodes on the stack,
/// and will always return `false` for the `on_stack` method.
pub struct TwoState(BitVec);

/// A three-state implementation of [`NodeState`].
///
/// This implementation does keep track of nodes on the stack, and will always
/// return the correct value for the `on_stack` method.
pub struct ThreeState(BitVec);

pub trait NodeState {
    fn set_on_stack(&mut self, node: usize);
    fn set_off_stack(&mut self, node: usize);
    fn on_stack(&self, node: usize) -> bool;
    fn set_known(&mut self, node: usize);
    fn known(&self, node: usize) -> bool;
    fn reset(&mut self);
}

impl ThreeState {
    fn new(n: usize) -> ThreeState {
        ThreeState(BitVec::new(2 * n))
    }
}
impl NodeState for ThreeState {
    #[inline(always)]
    fn set_on_stack(&mut self, node: usize) {
        self.0.set(node * 2 + 1, true);
    }
    #[inline(always)]
    fn set_off_stack(&mut self, node: usize) {
        self.0.set(node * 2 + 1, false);
    }
    #[inline(always)]
    fn on_stack(&self, node: usize) -> bool {
        self.0.get(node * 2 + 1)
    }
    #[inline(always)]
    fn set_known(&mut self, node: usize) {
        self.0.set(node * 2, true);
    }
    #[inline(always)]
    fn known(&self, node: usize) -> bool {
        self.0.get(node * 2)
    }
    #[inline(always)]
    fn reset(&mut self) {
        self.0.reset();
    }
}

impl TwoState {
    fn new(n: usize) -> TwoState {
        TwoState(BitVec::new(n))
    }
}

impl NodeState for TwoState {
    #[inline(always)]
    fn set_on_stack(&mut self, _node: usize) {}
    #[inline(always)]
    fn set_off_stack(&mut self, _node: usize) {}
    #[inline(always)]
    fn on_stack(&self, _node: usize) -> bool {
        false
    }
    #[inline(always)]
    fn set_known(&mut self, node: usize) {
        self.0.set(node, true);
    }
    #[inline(always)]
    fn known(&self, node: usize) -> bool {
        self.0.get(node)
    }
    #[inline(always)]
    fn reset(&mut self) {
        self.0.reset();
    }
}

impl<'a, S: NodeState, G: RandomAccessGraph> SeqVisit<Args>
    for SingleThreadedDepthFirstVisit<'a, S, G>
{
    fn visit_from_node<C: FnMut(Args), F: Fn(&Args) -> bool>(
        &mut self,
        root: usize,
        mut callback: C,
        filter: F,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) {
        let state = &mut self.state;

        if state.known(root) {
            return;
        }

        let args = Args {
            node: root,
            pred: root,
            root,
            depth: 0,
            event: Event::Unknown,
        };

        if !filter(&args) {
            // If the node is filtered, we consider its visit concluded
            // TODO
            return;
        }

        callback(args);

        self.stack
            .push((self.graph.successors(root).into_iter(), root));

        state.set_known(root);
        state.set_on_stack(root);

        // This variable keeps track of the current node being visited; the
        // parent node is derived at each iteration of the 'recurse loop.
        let mut current_node = root;

        'recurse: loop {
            let depth = self.stack.len();
            let Some((iter, parent)) = self.stack.last_mut() else {
                break;
            };
            let parent = *parent;

            for succ in iter {
                // Check if node should be visited
                if !state.known(succ) {
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
                        // current_node is the parent of succ
                        self.stack
                            .push((self.graph.successors(succ).into_iter(), current_node));
                        // At the next iteration, succ will be the current node

                        state.set_known(succ);
                        state.set_on_stack(succ);

                        current_node = succ;

                        continue 'recurse;
                    }
                } else {
                    // Node has already been visited

                    let args = Args {
                        node: succ,
                        pred: current_node,
                        root,
                        depth: depth + 1,
                        event: Event::Known(state.on_stack(succ)),
                    };
                    if !filter(&(args)) {
                        // We interrupt the visit
                        // TODOs
                        //return;
                    }
                    callback(args);
                }
            }

            pl.light_update();

            callback(Args {
                node: current_node,
                pred: parent,
                root,
                depth,
                event: Event::Completed,
            });

            state.set_off_stack(current_node);

            // We're going up one stack level, so the next current_node
            // is the current parent.
            current_node = parent;
            self.stack.pop();
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
        self.state.reset();
    }
}
