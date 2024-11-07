use crate::algo::visits::{breadth_first, breadth_first::Args, Sequential};
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use std::collections::VecDeque;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

use super::{Data, NodePred};
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
/// ```rust
/// use std::convert::Infallible;
/// use webgraph_algo::algo::visits::*;
/// use breadth_first::{Args, Data};
/// use dsi_progress_logger::no_logging;
/// use webgraph::graphs::vec_graph::VecGraph;
/// use webgraph::labels::proj::Left;
///
/// // Let's compute the distances from 0
///
/// let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3), (3, 3)]));
/// let mut visit = breadth_first::Seq::<Infallible, _>::new(&graph);
/// let mut d = [0; 4];
/// visit.visit(
///     0,
///     |&Args{
///         data,
///         root: _root,
///         distance,
///         event,
///     }|
///         {
///             // Set distance from 0
///             if event == breadth_first::Event::Unknown {
///                 d[data.curr()] = distance;
///             }
///             Ok(())
///         },
///    no_logging![]
/// );
/// assert_eq!(d, [0, 1, 2, 2]);

pub struct Seq<E, G: RandomAccessGraph> {
    graph: G,
    visited: BitVec,
    /// The visit queue; to avoid storing distances, we use `None` as a
    /// separator between levels. [`NonMaxUsize`] is used to avoid
    /// storage for the option variant tag.
    queue: VecDeque<Option<NonMaxUsize>>,
    _phantom: std::marker::PhantomData<E>,
}

impl<E, G: RandomAccessGraph> Seq<E, G> {
    /// Creates a new Sequential visit.
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

impl<E, G: RandomAccessGraph> Sequential<Args<NodePred>, E> for Seq<E, G> {
    fn visit_filtered<
        C: FnMut(&Args<NodePred>) -> Result<(), E>,
        F: FnMut(&Args<NodePred>) -> bool,
    >(
        &mut self,
        root: usize,
        mut callback: C,
        mut filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        let args = Args::<NodePred> {
            data: NodePred::new(root, root),
            root,
            distance: 0,
            event: breadth_first::Event::Unknown,
        };
        if self.visited[root] || !filter(&args) {
            return Ok(());
        }

        callback(&args)?;

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
                        let args = Args::<NodePred> {
                            data: NodePred::new(succ, node),
                            root,
                            distance,
                            event: breadth_first::Event::Unknown,
                        };
                        if filter(&args) {
                            if !self.visited[succ] {
                                callback(&args)?;
                                self.visited.set(succ, true);
                                self.queue.push_back(Some(
                                    NonMaxUsize::new(succ)
                                        .expect("node index should never be usize::MAX"),
                                ))
                            } else {
                                callback(&Args {
                                    data: Data::new(succ, node),
                                    root,
                                    distance,
                                    event: breadth_first::Event::Known,
                                })?;
                            }
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
        C: FnMut(&Args<NodePred>) -> Result<(), E>,
        F: FnMut(&Args<NodePred>) -> bool,
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
