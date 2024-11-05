use crate::algo::visits::{
    dfv::{Args, Event},
    SeqVisit,
};
use sux::bits::BitVec;
use sux::traits::BitFieldSliceMut;
use webgraph::traits::{RandomAccessGraph, RandomAccessLabeling};

/// A sequential depth-first visit.
///
/// This is an iterative implementation that does not depend on large stack
/// sizes to perform recursion.
///
/// There are two versions of the visit, selected by the parameter `S`. If `S`
/// is [`TwoState`], the visit will use a single bit per node to remember known
/// nodes, but events of type [`Event::Known`] will always have the associated
/// Boolean equal to `false` (this type of visit is sufficient, for example, to
/// compute a [topological sort](topsort)). If `S` is [`ThreeState`], instead,
/// the visit will use two bits per node and  events of type [`Event::Known`]
/// will provide information about whether the node associated with event is
/// currently on the visit stack (this kind of visit is necessary, for example,
/// to compute [acyclicity](aciclicity)).
pub struct SingleThreadedDepthFirstVisit<'a, S, E, G: RandomAccessGraph> {
    graph: &'a G,
    /// Entries on this stack represent the iterator on the successors of a node
    /// and the parent of the node. This approach makes it possible to avoid
    /// storing both the current and the parent node in the stack.
    stack: Vec<(
        <<G as RandomAccessLabeling>::Labels<'a> as IntoIterator>::IntoIter,
        usize,
    )>,
    state: S,
    _phantom: std::marker::PhantomData<E>,
}

impl<'a, E, G: RandomAccessGraph> SingleThreadedDepthFirstVisit<'a, ThreeState, E, G> {
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
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<'a, E, G: RandomAccessGraph> SingleThreadedDepthFirstVisit<'a, TwoState, E, G> {
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
            _phantom: std::marker::PhantomData,
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

trait NodeState {
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

impl<'a, S: NodeState, E, G: RandomAccessGraph> SeqVisit<Args, E>
    for SingleThreadedDepthFirstVisit<'a, S, E, G>
{
    fn visit_from_node_filtered<C: FnMut(&Args) -> Result<(), E>, F: FnMut(&Args) -> bool>(
        &mut self,
        root: usize,
        mut callback: C,
        mut filter: F,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Result<(), E> {
        let state = &mut self.state;

        if state.known(root) {
            return Ok(());
        }

        let args = Args {
            node: root,
            pred: root,
            root,
            depth: 0,
            event: Event::Unknown,
        };

        if !filter(&args) {
            // We ignore the node: it might be visited later
            return Ok(());
        }

        state.set_known(root);

        callback(&args)?;

        self.stack
            .push((self.graph.successors(root).into_iter(), root));

        state.set_on_stack(root);

        // This variable keeps track of the current node being visited; the
        // parent node is derived at each iteration of the 'recurse loop.
        let mut current_node = root;

        'recurse: loop {
            let depth = self.stack.len();
            let Some((iter, parent)) = self.stack.last_mut() else {
                return Ok(());
            };
            let parent = *parent;

            for succ in iter {
                // Check if node should be visited
                if state.known(succ) {
                    // Node has already been visited
                    let args = Args {
                        node: succ,
                        pred: current_node,
                        root,
                        depth: depth + 1,
                        event: Event::Known(state.on_stack(succ)),
                    };
                    if !filter(&args) {
                        // We interrupt the visit
                        return Ok(());
                    }
                    callback(&args)?;
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
                        state.set_known(succ);

                        callback(&args)?;
                        // current_node is the parent of succ
                        self.stack
                            .push((self.graph.successors(succ).into_iter(), current_node));

                        state.set_on_stack(succ);

                        // At the next iteration, succ will be the current node
                        current_node = succ;

                        continue 'recurse;
                    } // Else we ignore the node: it might be visited later
                }
            }

            pl.light_update();

            let args = Args {
                node: current_node,
                pred: parent,
                root,
                depth,
                event: Event::Completed,
            };

            if !filter(&args) {
                // We interrupt the visit
                return Ok(());
            }

            callback(&args)?;

            state.set_off_stack(current_node);

            // We're going up one stack level, so the next current_node
            // is the current parent.
            current_node = parent;
            self.stack.pop();
        }
    }

    fn visit<C: FnMut(&Args) -> Result<(), E>, F: FnMut(&Args) -> bool>(
        &mut self,
        mut callback: C,
        mut filter: F,
        pl: &mut impl dsi_progress_logger::ProgressLog,
    ) -> Result<(), E> {
        for node in 0..self.graph.num_nodes() {
            self.visit_from_node_filtered(node, &mut callback, &mut filter, pl)?;
        }

        Ok(())
    }

    fn reset(&mut self) {
        self.stack.clear();
        self.state.reset();
    }
}
