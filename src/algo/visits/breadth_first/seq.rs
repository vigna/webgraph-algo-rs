use crate::algo::visits::{
    breadth_first::{EventPred, FilterArgsPred},
    Sequential,
};
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use std::{collections::VecDeque, ops::ControlFlow, ops::ControlFlow::Continue};
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// A sequential breadth-first visit.
///
/// This implementation uses an algorithm that is slightly different from the
/// classical textbook algorithm, as we do not store parents or distances of the
/// nodes from the root: Parents and distances are computed on the fly and
/// passed to the callback function by visiting nodes when they are discovered,
/// rather than when they are extracted from the queue.
///
/// This approach requires inserting a level separator between nodes at
/// different distances: to obtain this result in a compact way, nodes are
/// represented using [`NonMaxUsize`], so the `None` variant of
/// `Option<NonMaxUsize>` can be used as a separator.
///
/// # Examples
///
/// Let's compute the distances from 0:
///
/// ```
/// use webgraph_algo::algo::visits::*;
/// use dsi_progress_logger::no_logging;
/// use webgraph::graphs::vec_graph::VecGraph;
/// use webgraph::labels::proj::Left;
/// use std::ops::ControlFlow::Continue;
/// use no_break::NoBreak;
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3)]));
/// let mut visit = breadth_first::Seq::new(&graph);
/// let mut d = [0; 4];
/// visit.visit(
///     0,
///     |event|
///         {
///             // Set distance from 0
///             if let breadth_first::EventPred::Unknown {curr, distance, ..} = event {
///                 d[curr] = distance;
///             }
///             Continue(())
///         },
///     no_logging![]
/// ).continue_value_no_break();
///
/// assert_eq!(d, [0, 1, 2, 2]);
/// ```
///
/// Here instead we compute the size of the ball of radius two around node 0: to
/// minimize resource usage, we count nodes in the filter function, rather than
/// as the result of an event. In this way, node at distance two are counted but
/// not included in the queue, as it would happen if we were counting during an
/// [`EventPred::Unknown`] event.
///
/// ```
/// use std::convert::Infallible;
/// use webgraph_algo::algo::visits::*;
/// use dsi_progress_logger::no_logging;
/// use webgraph::graphs::vec_graph::VecGraph;
/// use webgraph::labels::proj::Left;
/// use std::ops::ControlFlow::Continue;
/// use no_break::NoBreak;
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 3), (3, 0), (2, 4)]));
/// let mut visit = breadth_first::Seq::new(&graph);
/// let mut count = 0;
/// visit.visit_filtered(
///     0,
///     |event| { Continue(()) },
///     |breadth_first::FilterArgsPred { curr, distance, .. }|
///         {
///             if distance > 2 {
///                 false
///             } else {
///                 count += 1;
///                 true
///             }
///         },
///     no_logging![]
/// ).continue_value_no_break();
/// assert_eq!(count, 3);
/// ```
pub struct Seq<G: RandomAccessGraph> {
    graph: G,
    visited: BitVec,
    /// The visit queue; to avoid storing distances, we use `None` as a
    /// separator between levels. [`NonMaxUsize`] is used to avoid
    /// storage for the option variant tag.
    queue: VecDeque<Option<NonMaxUsize>>,
}

impl<G: RandomAccessGraph> Seq<G> {
    /// Creates a new sequential visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    pub fn new(graph: G) -> Self {
        let num_nodes = graph.num_nodes();
        Self {
            graph,
            visited: BitVec::new(num_nodes),
            queue: VecDeque::new(),
        }
    }
}

impl<G: RandomAccessGraph> Sequential<EventPred> for Seq<G> {
    fn visit_filtered<
        E,
        C: FnMut(EventPred) -> ControlFlow<E, ()>,
        F: FnMut(FilterArgsPred) -> bool,
        P: ProgressLog,
    >(
        &mut self,
        root: usize,
        mut callback: C,
        mut filter: F,
        pl: &mut P,
    ) -> ControlFlow<E, ()> {
        if self.visited[root]
            || !filter(FilterArgsPred {
                node: root,
                pred: root,
                root,
                distance: 0,
            })
        {
            return Continue(());
        }

        self.visited.set(root, true);
        pl.light_update();
        callback(EventPred::Unknown {
            node: root,
            pred: root,
            root,
            distance: 0,
        })?;

        self.queue.push_back(Some(
            NonMaxUsize::new(root).expect("node index should never be usize::MAX"),
        ));
        self.queue.push_back(None);

        let mut distance = 1;

        while let Some(current_node) = self.queue.pop_front() {
            match current_node {
                Some(node) => {
                    let node = node.into();
                    for succ in self.graph.successors(node) {
                        let (node, pred) = (succ, node);
                        if !self.visited[succ] {
                            if filter(FilterArgsPred {
                                node,
                                pred,
                                root,
                                distance,
                            }) {
                                self.visited.set(succ, true);
                                pl.light_update();
                                callback(EventPred::Unknown {
                                    node,
                                    pred,
                                    root,
                                    distance,
                                })?;
                                self.queue.push_back(Some(
                                    NonMaxUsize::new(succ)
                                        .expect("node index should never be usize::MAX"),
                                ))
                            }
                        } else {
                            callback(EventPred::Known { node, pred, root })?;
                        }
                    }
                }
                None => {
                    // We are at the end of the current level, so
                    // we increment the distance and add a separator.
                    if !self.queue.is_empty() {
                        distance += 1;
                        self.queue.push_back(None);
                    }
                }
            }
        }

        callback(EventPred::Done { root })?;

        Continue(())
    }

    fn visit_all_filtered<
        E,
        C: FnMut(EventPred) -> ControlFlow<E, ()>,
        F: FnMut(FilterArgsPred) -> bool,
        P: ProgressLog,
    >(
        &mut self,
        mut callback: C,
        mut filter: F,
        pl: &mut P,
    ) -> ControlFlow<E, ()> {
        for node in 0..self.graph.num_nodes() {
            self.visit_filtered(node, &mut callback, &mut filter, pl)?;
        }

        Continue(())
    }

    fn reset(&mut self) {
        self.queue.clear();
        self.visited.fill(false);
    }
}
