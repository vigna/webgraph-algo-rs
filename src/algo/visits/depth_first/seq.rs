use crate::algo::visits::{
    depth_first::{Event, EventPred, FilterArgs, FilterArgsPred},
    Sequential,
};
use dsi_progress_logger::ProgressLog;
use sealed::sealed;
use sux::bits::BitVec;
use sux::traits::BitFieldSliceMut;
use webgraph::traits::{RandomAccessGraph, RandomAccessLabeling};

/// A depth-first visit which does not keep track of predecessors, or nodes on the stack.
pub type Seq<'a, G> = SeqIter<'a, TwoStates, G, (), false>;

/// A depth-first visit which keeps track of predecessors, but not nodes on the stack.
pub type SeqPred<'a, G> = SeqIter<'a, TwoStates, G, usize, true>;

/// A depth-first visit which keeps track of predecessors and nodes on the stack.
pub type SeqPath<'a, G> = SeqIter<'a, ThreeStates, G, usize, true>;

/// Sequential depth-first visits.
///
/// This is an iterative implementation that does not need a large stack size.
///
/// There are three version of the visit, which are type aliases to the same
/// common implementation: [`Seq`], [`SeqPred`] and [`SeqPath`] (the generic
/// implementation should not be instantiated by the user).
///
/// * [`Seq`] does not keep track of predecessors, nor of nodes on the stack; it
///   can be used, for example, to compute reachability information.
/// * [`SeqPred`] keeps track of predecessors, but not of nodes on the stack; it
///   can be used, for example, to compute a [topological
///   sort](crate::algo::top_sort).
/// * [`SeqPath`] keeps track of predecessors and nodes on the stack; it can be
///   used, for example, to establish [acyclicity](crate::algo::acyclicity).
///
/// Each type of visit uses incrementally more space:
/// * [`Seq`] uses one bit per node to remember known nodes and a stack of
///   iterators, one for each node on the visit path.
/// * [`SeqPred`] uses one bit per node to remember known nodes and a stack of
///   pairs made of an iterator and a predecessor, one for each node on the
///   visit path.
/// * [`SeqPath`] uses two bits per node to remember known nodes and whether the
///   node is on the visit path, and a stack of pairs made of an iterator and a
///   predecessor, one for each node on the visit path.
///
/// The visits differ also in the type of events they generate:
/// * [`Seq`] generates events of type [`Event`].
/// * [`SeqPred`] generates events of type [`EventPred`], with the proviso that
///   the Boolean associated with events of type [`Revisit`](`Event::Revisit`)
///   is always false.
/// * [`SeqPath`] generates events of type [`EventPred`].
///
/// The arguments for callbacks are of type [`Event`] for [`Seq`] and of type
/// [`EventPred`] for [`SeqPred`] and [`SeqPath`]. With respect to [`Event`],
/// [`EventPred`] adds the predecessor of the current node to the data field,
/// and provides a [postvisit event](EventPred::Postvisit).
///
/// All visits accept two type parameters: an error type to be returned in case
/// the visit must be interrupted (for example,
/// [`StoppedWhenDone`](crate::algo::visits::StoppedWhenDone) when completing
/// early, [`Interrupted`](crate::algo::visits::Interrupted) when interrupted or
/// [`Infallible`](std::convert::Infallible) if the visit cannot be
/// interrupted), and a
/// [`RandomAccessGraph`](webgraph::traits::RandomAccessGraph). These are
/// usually taken care of by type inference.
///
/// If the visit was interrupted, the nodes still on the visit path can be
/// retrieved using the [`stack`](Seq::stack) method (only for [`SeqPred`] and
/// [`SeqPath`]).
///
/// # Examples
///
/// ```
/// use webgraph_algo::algo::visits::*;
/// use webgraph_algo::algo::visits::depth_first::*;
/// use dsi_progress_logger::no_logging;
/// use webgraph::graphs::vec_graph::VecGraph;
/// use webgraph::labels::proj::Left;
///
/// // Let's test acyclicity.
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3), (3, 3)]));
/// let mut visit = depth_first::SeqPath::new(&graph);
///
/// assert!(visit.visit_all(
///     |event|
///         {
///             // Stop the visit as soon as a back edge is found
///            match event {
///                EventPred::Revisit { on_stack: true, .. } => Err(StoppedWhenDone {}),
///                _ => Ok(()),
///            }
///         },
///         no_logging![]
///     ).is_err()); // As the graph is not acyclic
/// ```

// General depth-first visit implementation. The user shouldn't see this.
// Allowed combinations for `PRED`, `S` and `P` are:
// * `false`, `TwoStates` and `()` (no predecessors, no stack tracking)
// * `true`, `TwoStates` and `usize` (predecessors, no stack tracking)
// * `true`, `ThreeStates` and `usize` (predecessors, stack tracking)
pub struct SeqIter<'a, S, G: RandomAccessGraph, P, const PRED: bool> {
    graph: &'a G,
    /// Entries on this stack represent the iterator on the successors of a node
    /// and the parent of the node. This approach makes it possible to avoid
    /// storing both the current and the parent node in the stack.
    stack: Vec<(
        <<G as RandomAccessLabeling>::Labels<'a> as IntoIterator>::IntoIter,
        P,
    )>,
    state: S,
}

/// The iterator returned by [`stack`](Seq::stack).
pub struct StackIterator<'a, 'b, S, G: RandomAccessGraph> {
    visit: &'b mut SeqIter<'a, S, G, usize, true>,
}

impl<'a, 'b, S, G: RandomAccessGraph> Iterator for StackIterator<'a, 'b, S, G> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        self.visit.stack.pop().map(|(_, parent)| parent)
    }
}

impl<'a, S: NodeStates, G: RandomAccessGraph, P, const PRED: bool> SeqIter<'a, S, G, P, PRED> {
    /// Creates a new sequential visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new(graph: &'a G) -> SeqIter<'a, S, G, P, PRED> {
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            stack: Vec::with_capacity(16),
            state: S::new(num_nodes),
        }
    }
}

impl<'a, S, G: RandomAccessGraph> SeqIter<'a, S, G, usize, true> {
    /// Returns an iterator over the nodes stil on the visit path.
    ///
    /// Node will be returned in reverse order of visit.
    ///
    /// This method is useful only in the case of interrupted visits,
    /// as in a completed visit the stack will be empty.
    pub fn stack(&mut self) -> StackIterator<'a, '_, S, G> {
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

#[doc(hidden)]
/// A two-state selector type for [sequential depth-first visits](Seq).
///
/// This implementation does not keep track of nodes on the stack,
/// so events of type [`Revisit`](`Event::Revisit`) will always have the
/// associated Boolean equal to false.
pub struct TwoStates(BitVec);

#[doc(hidden)]
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

impl<'a, S: NodeStates, G: RandomAccessGraph> Sequential<EventPred>
    for SeqIter<'a, S, G, usize, true>
{
    fn visit_filtered<E, C: FnMut(EventPred) -> Result<(), E>, F: FnMut(FilterArgsPred) -> bool>(
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

        if !filter(FilterArgsPred {
            curr: root,
            pred: root,
            root,
            depth: 0,
        }) {
            // We ignore the node: it might be visited later
            return Ok(());
        }

        state.set_known(root);

        callback(EventPred::Previsit {
            curr: root,
            pred: root,
            root,
            depth: 0,
        })?;

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
                    callback(EventPred::Revisit {
                        curr: succ,
                        pred: current_node,
                        root,
                        depth: depth + 1,
                        on_stack: state.on_stack(succ),
                    })?;
                } else {
                    // First time seeing node
                    if filter(FilterArgsPred {
                        curr: succ,
                        pred: current_node,
                        root,
                        depth: depth + 1,
                    }) {
                        state.set_known(succ);

                        callback(EventPred::Previsit {
                            curr: succ,
                            pred: current_node,
                            root,
                            depth: depth + 1,
                        })?;
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

            callback(EventPred::Postvisit {
                curr: current_node,
                pred: *parent,
                root,
                depth,
            })?;

            state.set_off_stack(current_node);

            // We're going up one stack level, so the next current_node
            // is the current parent.
            current_node = *parent;
            self.stack.pop();
        }
    }

    fn visit_all_filtered<
        E,
        C: FnMut(EventPred) -> Result<(), E>,
        F: FnMut(FilterArgsPred) -> bool,
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

impl<'a, G: RandomAccessGraph> Sequential<Event> for SeqIter<'a, TwoStates, G, (), false> {
    fn visit_filtered<E, C: FnMut(Event) -> Result<(), E>, F: FnMut(FilterArgs) -> bool>(
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

        if !filter(FilterArgs {
            curr: root,
            root,
            depth: 0,
        }) {
            // We ignore the node: it might be visited later
            return Ok(());
        }

        state.set_known(root);

        callback(Event::Previsit {
            curr: root,
            root,
            depth: 0,
        })?;

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
                    callback(Event::Revisit {
                        curr: succ,
                        root,
                        depth: depth + 1,
                    })?;
                } else {
                    // First time seeing node
                    if filter(FilterArgs {
                        curr: succ,
                        root,
                        depth: depth + 1,
                    }) {
                        state.set_known(succ);

                        callback(Event::Previsit {
                            curr: succ,
                            root,
                            depth: depth + 1,
                        })?;
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

    fn visit_all_filtered<E, C: FnMut(Event) -> Result<(), E>, F: FnMut(FilterArgs) -> bool>(
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
