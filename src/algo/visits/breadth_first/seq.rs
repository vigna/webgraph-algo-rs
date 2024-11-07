use crate::algo::visits::{
    breadth_first::{EventPred, FilterArgsPred},
    Sequential,
};
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use std::collections::VecDeque;
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
/// ```
/// use std::convert::Infallible;
/// use webgraph_algo::algo::visits::*;
/// use dsi_progress_logger::no_logging;
/// use webgraph::graphs::vec_graph::VecGraph;
/// use webgraph::labels::proj::Left;
///
/// // Let's compute the distances from 0
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3), (3, 3)]));
/// let mut visit = breadth_first::Seq::<_>::new(&graph);
/// let mut d = [0; 4];
/// visit.visit(
///     0,
///     |args|
///         {
///             // Set distance from 0
///             if let breadth_first::EventPred::Unknown {curr, distance, ..} = args {
///                 d[curr] = distance;
///             }
///             Ok(())
///         },
///    no_logging![]
/// ).unwrap();
/// assert_eq!(d, [0, 1, 2, 2]);
/// ```
pub struct Seq<G: RandomAccessGraph, E = std::convert::Infallible> {
    graph: G,
    visited: BitVec,
    /// The visit queue; to avoid storing distances, we use `None` as a
    /// separator between levels. [`NonMaxUsize`] is used to avoid
    /// storage for the option variant tag.
    queue: VecDeque<Option<NonMaxUsize>>,
    _phantom: std::marker::PhantomData<E>,
}

impl<G: RandomAccessGraph, E> Seq<G, E> {
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
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<G: RandomAccessGraph, E> Sequential<EventPred, E> for Seq<G, E> {
    fn visit_filtered<C: FnMut(EventPred) -> Result<(), E>, F: FnMut(FilterArgsPred) -> bool>(
        &mut self,
        root: usize,
        mut callback: C,
        mut filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        if self.visited[root]
            || !filter(FilterArgsPred {
                curr: root,
                pred: root,
                root,
                distance: 0,
            })
        {
            return Ok(());
        }

        callback(EventPred::Unknown {
            curr: root,
            pred: root,
            root,
            distance: 0,
        })?;

        self.visited.set(root, true);
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
                        let (curr, pred) = (succ, node);
                        if !self.visited[succ] {
                            if filter(FilterArgsPred {
                                curr,
                                pred,
                                root,
                                distance,
                            }) {
                                callback(EventPred::Unknown {
                                    curr,
                                    pred,
                                    root,
                                    distance,
                                })?;
                                self.visited.set(succ, true);
                                self.queue.push_back(Some(
                                    NonMaxUsize::new(succ)
                                        .expect("node index should never be usize::MAX"),
                                ))
                            }
                        } else {
                            callback(EventPred::Known { curr, pred, root })?;
                        }
                    }
                    pl.light_update();
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

        Ok(())
    }

    fn visit_all_filtered<
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
        self.queue.clear();
        self.visited.fill(false);
    }
}
