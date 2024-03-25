use crate::prelude::*;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;
use std::{collections::VecDeque, marker::PhantomData};
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

pub struct SingleThreadedBreadthFirstIterator<'a, G: RandomAccessGraph, N, F: NodeFactory<Node = N>>
{
    graph: &'a G,
    start: usize,
    node_factory: &'a F,
    visited: BitVec,
    queue: VecDeque<usize>,
    _node_type: PhantomData<N>,
}

pub struct SingleThreadedBreadthFirstVisit<
    'a,
    G: RandomAccessGraph,
    N: NodeVisit,
    F: NodeFactory<Node = N>,
> {
    graph: &'a G,
    start: usize,
    node_factory: &'a F,
    _node_type: PhantomData<N>,
}

impl<'a, G: RandomAccessGraph, N, F: NodeFactory<Node = N>> Iterator
    for SingleThreadedBreadthFirstIterator<'a, G, N, F>
{
    type Item = N;
    fn next(&mut self) -> Option<N> {
        let current_node_index = match self.queue.pop_front() {
            None => {
                while self.visited[self.start] {
                    self.start += 1;
                    if self.start >= self.graph.num_nodes() {
                        return None;
                    }
                }
                self.visited.set(self.start, true);
                self.start
            }
            Some(node) => node,
        };

        for successor in self.graph.successors(current_node_index) {
            if !self.visited[successor] {
                self.queue.push_back(successor);
                self.visited.set(successor, true);
            }
        }

        Some(self.node_factory.node_from_index(current_node_index))
    }
}

impl<'a, G: RandomAccessGraph, N: NodeVisit, F: NodeFactory<Node = N>>
    SingleThreadedBreadthFirstVisit<'a, G, N, F>
{
    pub fn new(graph: &'a G, node_factory: &'a F) -> SingleThreadedBreadthFirstVisit<'a, G, N, F> {
        Self::with_start(graph, node_factory, 0)
    }

    pub fn with_start(
        graph: &'a G,
        node_factory: &'a F,
        start: usize,
    ) -> SingleThreadedBreadthFirstVisit<'a, G, N, F> {
        SingleThreadedBreadthFirstVisit {
            graph,
            start,
            node_factory,
            _node_type: PhantomData,
        }
    }
}

impl<'a, G: RandomAccessGraph, N: NodeVisit, F: NodeFactory<Node = N>> IntoIterator
    for SingleThreadedBreadthFirstVisit<'a, G, N, F>
{
    type Item = N;
    type IntoIter = SingleThreadedBreadthFirstIterator<'a, G, N, F>;
    fn into_iter(self) -> SingleThreadedBreadthFirstIterator<'a, G, N, F> {
        SingleThreadedBreadthFirstIterator {
            graph: self.graph,
            start: self.start,
            visited: BitVec::new(self.graph.num_nodes()),
            queue: VecDeque::new(),
            node_factory: self.node_factory,
            _node_type: PhantomData,
        }
    }
}

impl<'a, G: RandomAccessGraph, N: NodeVisit, F: NodeFactory<Node = N>> IntoIterator
    for &SingleThreadedBreadthFirstVisit<'a, G, N, F>
{
    type Item = N;
    type IntoIter = SingleThreadedBreadthFirstIterator<'a, G, N, F>;
    fn into_iter(self) -> SingleThreadedBreadthFirstIterator<'a, G, N, F> {
        SingleThreadedBreadthFirstIterator {
            graph: self.graph,
            start: self.start,
            visited: BitVec::new(self.graph.num_nodes()),
            queue: VecDeque::new(),
            node_factory: self.node_factory,
            _node_type: PhantomData,
        }
    }
}

impl<'a, G: RandomAccessGraph, N: NodeVisit, F: NodeFactory<Node = N>> IntoIterator
    for &mut SingleThreadedBreadthFirstVisit<'a, G, N, F>
{
    type Item = N;
    type IntoIter = SingleThreadedBreadthFirstIterator<'a, G, N, F>;
    fn into_iter(self) -> SingleThreadedBreadthFirstIterator<'a, G, N, F> {
        SingleThreadedBreadthFirstIterator {
            graph: self.graph,
            start: self.start,
            visited: BitVec::new(self.graph.num_nodes()),
            queue: VecDeque::new(),
            node_factory: self.node_factory,
            _node_type: PhantomData,
        }
    }
}

impl<'a, G: RandomAccessGraph, N: NodeVisit, F: NodeFactory<Node = N>> GraphVisit<N>
    for SingleThreadedBreadthFirstVisit<'a, G, N, F>
{
    fn visit(self, mut pl: impl ProgressLog) -> Result<N::AccumulatedResult> {
        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Visiting graph with a sequential BFV...");
        let mut result = N::init_result();
        for node in self {
            pl.light_update();
            N::accumulate_result(&mut result, node.visit());
        }
        pl.done();
        Ok(result)
    }
}
