use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use std::collections::VecDeque;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// Builder for [`SingleThreadedBreadthFirstVisit`].
#[derive(Clone)]
pub struct SingleThreadedBreadthFirstVisitBuilder<'a, G: RandomAccessGraph> {
    graph: &'a G,
}

impl<'a, G: RandomAccessGraph> SingleThreadedBreadthFirstVisitBuilder<'a, G> {
    /// Constructs a new builder with default parameters for specified graph.
    pub fn new(graph: &'a G) -> Self {
        Self { graph }
    }

    /// Builds the sequential BFV with the builder parameters and consumes the builder.
    pub fn build(self) -> SingleThreadedBreadthFirstVisit<'a, G> {
        SingleThreadedBreadthFirstVisit {
            graph: self.graph,
            visited: BitVec::new(self.graph.num_nodes()),
            queue: VecDeque::new(),
        }
    }
}

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
pub struct SingleThreadedBreadthFirstVisit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    visited: BitVec,
    /// The visit queue; to avoid storing distances, we use `None` as a
    /// separator between levels. [`NonMaxUsize`] is used to avoid
    /// storage for the option variant tag.
    queue: VecDeque<Option<NonMaxUsize>>,
}

impl<'a, G: RandomAccessGraph> BreadthFirstGraphVisit for SingleThreadedBreadthFirstVisit<'a, G> {
    fn visit_from_node_filtered<C: Fn(BFVArgs) + Sync, F: Fn(BFVArgs) -> bool + Sync>(
        &mut self,
        callback: C,
        filter: F,
        visit_root: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        let args = BFVArgs {
            node_index: visit_root,
            parent: visit_root,
            root: visit_root,
            distance_from_root: 0,
        };
        if self.visited[visit_root] || !filter(args) {
            return Ok(());
        }

        callback(args);
        self.visited.set(visit_root, true);
        self.queue.push_back(Some(
            NonMaxUsize::new(visit_root).expect("node index should never be usize::MAX"),
        ));
        self.queue.push_back(None);

        let mut distance = 1;

        while let Some(current_node) = self.queue.pop_front() {
            let current_node = current_node.map(|n| n.into());
            match current_node {
                Some(node) => {
                    for succ in self.graph.successors(node) {
                        let args = BFVArgs {
                            node_index: succ,
                            parent: node,
                            root: visit_root,
                            distance_from_root: distance,
                        };
                        if !self.visited[succ] && filter(args) {
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

        Ok(())
    }

    #[inline(always)]
    fn reset(&mut self) -> Result<()> {
        self.queue.clear();
        self.visited.fill(false);
        Ok(())
    }
}
