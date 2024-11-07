use crate::algo::visits::{
    depth_first::{Args, Event},
    Data, Node, NodePred, Sequential,
};
use dsi_progress_logger::ProgressLog;
use sealed::sealed;
use sux::bits::BitVec;
use sux::traits::BitFieldSliceMut;
use webgraph::traits::{RandomAccessGraph, RandomAccessLabeling};

use super::EventPred;

/// A sequential depth-first visit.
///
/// This is an iterative implementation that does not depend on large stack
/// sizes to perform recursion.
///
/// There are two versions of the visit, selected by the parameter `S`. If `S`
/// is [`TwoStates`], the visit will use a single bit per node to remember known
/// nodes, but events of type [`Revisit`](`Event::Revisit`) will always have the
/// associated Boolean equal to false (this type of visit is sufficient, for
/// example, to compute a [topological sort](crate::algo::top_sort)). If `S` is
/// [`ThreeStates`], instead, the visit will use two bits per node and  events of
/// type [`Revisit`](`Event::Revisit`) will provide information about whether
/// the node associated with event is currently on the visit path (this kind of
/// visit is necessary, for example, to compute
/// [acyclicity](crate::algo::acyclicity)).
///
/// If the visit was interrupted, the nodes still on the visit path can be
/// retrieved using the [`stack`](Seq::stack) method.
///
/// # Examples
///
/// ```rust
/// use webgraph_algo::algo::visits::*;
/// use webgraph_algo::algo::visits::depth_first::*;
/// use dsi_progress_logger::no_logging;
/// use webgraph::graphs::vec_graph::VecGraph;
/// use webgraph::labels::proj::Left;
///
/// // Let's test acyclicity.
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3), (3, 3)]));
/// let mut visit = depth_first::Seq::<NodePred, ThreeStates, _, _, _>::new(&graph);
///
/// assert!(visit.visit_all(
///        |args|
///          {
///            // Stop the visit as soon as a back edge is found
///            if args.event == EventPred::Revisit(true) {
///                Err(StoppedWhenDone {})
///            } else {
///                Ok(())
///            }
///        },
///        no_logging![]
///    ).is_err()); // As the graph is not acyclic

pub struct Seq<'a, D, S, E, G: RandomAccessGraph, P> {
    graph: &'a G,
    /// Entries on this stack represent the iterator on the successors of a node
    /// and the parent of the node. This approach makes it possible to avoid
    /// storing both the current and the parent node in the stack.
    stack: Vec<(
        <<G as RandomAccessLabeling>::Labels<'a> as IntoIterator>::IntoIter,
        P,
    )>,
    state: S,
    _phantom: std::marker::PhantomData<(D, E)>,
}

/// The iterator returned by the [`stack`](Seq::stack).
pub struct StackIterator<'a, 'b, S, E, G: RandomAccessGraph> {
    visit: &'b mut Seq<'a, NodePred, S, E, G, usize>,
}

impl<'a, 'b, S, E, G: RandomAccessGraph> Iterator for StackIterator<'a, 'b, S, E, G> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        self.visit.stack.pop().map(|(_, parent)| parent)
    }
}

impl<'a, D, S: NodeStates, E, G: RandomAccessGraph, P> Seq<'a, D, S, E, G, P> {
    /// Creates a new sequential visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> Seq<'a, D, S, E, G, P> {
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            stack: Vec::with_capacity(16),
            state: S::new(num_nodes),
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<'a, S, E, G: RandomAccessGraph> Seq<'a, NodePred, S, E, G, usize> {
    /// Returns an iterator over the nodes stil on the visit path.
    ///
    /// Node will be returned in reverse order of visit.
    ///
    /// This method is useful only in the case of interrupted visits,
    /// as in a completed visit the stack will be empty.
    pub fn stack(&mut self) -> StackIterator<'a, '_, S, E, G> {
        StackIterator { visit: self }
    }
}

#[doc(hidden)]
#[sealed]
pub trait NodeStates {
    fn new(n: usize) -> Self;
    fn set_on_stack(&mut self, node: usize);
    fn set_off_stack(&mut self, node: usize);
    fn on_stack(&self, node: usize) -> bool;
    fn set_known(&mut self, node: usize);
    fn known(&self, node: usize) -> bool;
    fn reset(&mut self);
}

/// A two-state selector type for [sequential depth-first visits](Seq).
///
/// This implementation does not keep track of nodes on the stack,
/// so events of type [`Revisit`](`Event::Revisit`) will always have the
/// associated Boolean equal to false.
pub struct TwoStates(BitVec);

/// A three-state selector type for [sequential depth-first visits](Seq).
///
/// This implementation does keep track of nodes on the stack, so events of type
/// [`Revisit`](`Event::Revisit`) will provide information about whether the
/// node associated with event is currently on the visit path.
pub struct ThreeStates(BitVec);

#[sealed]
impl NodeStates for ThreeStates {
    fn new(n: usize) -> ThreeStates {
        ThreeStates(BitVec::new(2 * n))
    }
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

#[sealed]
impl NodeStates for TwoStates {
    fn new(n: usize) -> TwoStates {
        TwoStates(BitVec::new(n))
    }
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

impl<'a, S: NodeStates, E, G: RandomAccessGraph> Sequential<Args<NodePred, EventPred>, E>
    for Seq<'a, NodePred, S, E, G, usize>
{
    fn visit_filtered<
        C: FnMut(&Args<NodePred, EventPred>) -> Result<(), E>,
        F: FnMut(&Args<NodePred, EventPred>) -> bool,
    >(
        &mut self,
        root: usize,
        mut callback: C,
        mut filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        let state = &mut self.state;

        if state.known(root) {
            return Ok(());
        }

        let args = Args {
            data: NodePred::new(root, root),
            root,
            depth: 0,
            event: EventPred::Previsit,
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

            for succ in iter {
                // Check if node should be visited
                if state.known(succ) {
                    // Node has already been discovered
                    callback(&Args {
                        data: NodePred::new(succ, current_node),
                        root,
                        depth: depth + 1,
                        event: EventPred::Revisit(state.on_stack(succ)),
                    })?;
                } else {
                    // First time seeing node
                    let args = Args {
                        data: NodePred::new(succ, current_node),
                        root,
                        depth: depth + 1,
                        event: EventPred::Previsit,
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

            callback(
                &(Args {
                    data: NodePred::new(current_node, *parent),
                    root,
                    depth,
                    event: EventPred::Postvisit,
                }),
            )?;

            state.set_off_stack(current_node);

            // We're going up one stack level, so the next current_node
            // is the current parent.
            current_node = *parent;
            self.stack.pop();
        }
    }

    fn visit_all_filtered<
        C: FnMut(&Args<NodePred, EventPred>) -> Result<(), E>,
        F: FnMut(&Args<NodePred, EventPred>) -> bool,
    >(
        &mut self,
        mut callback: C,
        mut filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        for node in 0..self.graph.num_nodes() {
            self.visit_filtered(node, &mut callback, &mut filter, pl)?;
        }

        Ok(())
    }

    fn reset(&mut self) {
        self.stack.clear();
        self.state.reset();
    }
}

impl<'a, E, G: RandomAccessGraph> Sequential<Args<Node, Event>, E>
    for Seq<'a, Node, TwoStates, E, G, ()>
{
    fn visit_filtered<
        C: FnMut(&Args<Node, Event>) -> Result<(), E>,
        F: FnMut(&Args<Node, Event>) -> bool,
    >(
        &mut self,
        root: usize,
        mut callback: C,
        mut filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        let state = &mut self.state;

        if state.known(root) {
            return Ok(());
        }

        let args = Args {
            data: Node { curr: root },
            root,
            depth: 0,
            event: Event::Previsit,
        };

        if !filter(&args) {
            // We ignore the node: it might be visited later
            return Ok(());
        }

        state.set_known(root);

        callback(&args)?;

        self.stack
            .push((self.graph.successors(root).into_iter(), ()));

        'recurse: loop {
            let depth = self.stack.len();
            let Some((iter, _)) = self.stack.last_mut() else {
                return Ok(());
            };

            for succ in iter {
                // Check if node should be visited
                if state.known(succ) {
                    // Node has already been discovered
                    callback(&Args {
                        data: Node { curr: succ },
                        root,
                        depth: depth + 1,
                        event: Event::Revisit(false),
                    })?;
                } else {
                    // First time seeing node
                    let args = Args {
                        data: Node { curr: succ },
                        root,
                        depth: depth + 1,
                        event: Event::Previsit,
                    };

                    if filter(&args) {
                        state.set_known(succ);

                        callback(&args)?;
                        // current_node is the parent of succ
                        self.stack
                            .push((self.graph.successors(succ).into_iter(), ()));

                        continue 'recurse;
                    } // Else we ignore the node: it might be visited later
                }
            }

            pl.light_update();

            // We're going up one stack level, so the next current_node
            // is the current parent.
            self.stack.pop();
        }
    }

    fn visit_all_filtered<
        C: FnMut(&Args<Node, Event>) -> Result<(), E>,
        F: FnMut(&Args<Node, Event>) -> bool,
    >(
        &mut self,
        mut callback: C,
        mut filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        for node in 0..self.graph.num_nodes() {
            self.visit_filtered(node, &mut callback, &mut filter, pl)?;
        }

        Ok(())
    }

    fn reset(&mut self) {
        self.stack.clear();
        self.state.reset();
    }
}
