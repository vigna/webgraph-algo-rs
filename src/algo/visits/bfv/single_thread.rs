use crate::algo::visits::{bfv, SeqVisit};
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use std::collections::VecDeque;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// A simple sequential Breadth First visit on a graph.
///
/// This implementation uses an algorithm that is slightly different from the
/// classical textbook one, as it does not store parents or distances of the
/// nodes from the root. Parents and distances are computed on the fly and
/// passed to the callback function by visiting nodes when they are discovered,
/// rather than when they are extracted from the queue. This approach requires
/// inserting a level separator between nodes at different distances: to
/// obtain this result in a compact way, nodes are represented using
/// [`NonMaxUsize`], so the `None` variant of `Option<NonMaxUsize>`
/// can be used as a separator.
pub struct SingleThreadedBreadthFirstVisit<G: RandomAccessGraph> {
    graph: G,
    visited: BitVec,
    /// The visit queue; to avoid storing distances, we use `None` as a
    /// separator between levels. [`NonMaxUsize`] is used to avoid
    /// storage for the option variant tag.
    queue: VecDeque<Option<NonMaxUsize>>,
}

impl<G: RandomAccessGraph> SingleThreadedBreadthFirstVisit<G> {
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

impl<G: RandomAccessGraph> SeqVisit<bfv::Args> for SingleThreadedBreadthFirstVisit<G> {
    fn visit_from_node<C: FnMut(bfv::Args), F: Fn(&bfv::Args) -> bool>(
        &mut self,
        root: usize,
        mut callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) {
        let args = bfv::Args {
            node: root,
            parent: root,
            root,
            distance: 0,
        };
        if self.visited[root] || !filter(&args) {
            return;
        }

        self.visited.set(root, true);
        self.queue.push_back(Some(
            NonMaxUsize::new(root).expect("node index should never be usize::MAX"),
        ));
        self.queue.push_back(None);

        let mut distance = 1;

        while let Some(current_node) = self.queue.pop_front() {
            let current_node = current_node.map(|n| n.into());
            match current_node {
                Some(node) => {
                    for succ in self.graph.successors(node) {
                        let args = bfv::Args {
                            node: succ,
                            parent: node,
                            root,
                            distance,
                        };
                        if !self.visited[succ] && filter(&args) {
                            callback(args);
                            self.visited.set(succ, true);
                            self.queue.push_back(Some(
                                NonMaxUsize::new(succ)
                                    .expect("node index should never be usize::MAX"),
                            ))
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
    }

    fn visit<C: FnMut(bfv::Args), F: Fn(&bfv::Args) -> bool>(
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
        self.queue.clear();
        self.visited.fill(false);
    }
}
