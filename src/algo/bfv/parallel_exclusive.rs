use crate::prelude::*;
use anyhow::{Context, Ok, Result};
use dsi_progress_logger::ProgressLog;
use rayon::{join, prelude::*};
use rayon::{ThreadPool, ThreadPoolBuilder};
use std::{
    marker::PhantomData,
    sync::{Arc, Mutex},
    thread::available_parallelism,
};
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

pub struct ParallelExclusiveBreadthFirstVisit<
    'a,
    G: RandomAccessGraph,
    N: NodeVisit,
    F: NodeFactory<Node = N>,
> {
    graph: &'a G,
    start: usize,
    node_factory: &'a F,
    thread_pool: Option<ThreadPool>,
    _node_type: PhantomData<N>,
}

impl<'a, G: RandomAccessGraph, N: NodeVisit, F: NodeFactory<Node = N>>
    ParallelExclusiveBreadthFirstVisit<'a, G, N, F>
{
    fn build(
        graph: &'a G,
        start: usize,
        node_factory: &'a F,
        pool: Option<ThreadPool>,
    ) -> ParallelExclusiveBreadthFirstVisit<'a, G, N, F> {
        ParallelExclusiveBreadthFirstVisit {
            graph,
            start,
            node_factory,
            thread_pool: pool,
            _node_type: PhantomData,
        }
    }

    pub fn with_start(
        graph: &'a G,
        node_factory: &'a F,
        start: usize,
    ) -> ParallelExclusiveBreadthFirstVisit<'a, G, N, F> {
        Self::build(graph, start, node_factory, None)
    }

    pub fn new(
        graph: &'a G,
        node_factory: &'a F,
    ) -> ParallelExclusiveBreadthFirstVisit<'a, G, N, F> {
        Self::with_start(graph, node_factory, 0)
    }
}

impl<
        'a,
        G: RandomAccessGraph + Sync,
        R: Send,
        N: NodeVisit<AccumulatedResult = R>,
        F: NodeFactory<Node = N> + Sync,
    > GraphVisit<N> for ParallelExclusiveBreadthFirstVisit<'a, G, N, F>
{
    fn visit(self, mut pl: impl ProgressLog) -> Result<N::AccumulatedResult> {
        let result = Arc::new(Mutex::new(N::init_result()));
        let visited_ref = Arc::new(Mutex::new(BitVec::new(self.graph.num_nodes())));
        let mut current_frontier = Vec::new();
        let next_frontier_ref = Arc::new(Mutex::new(Vec::new()));
        let mut start = self.start;
        let threads = match self.thread_pool {
            Some(t) => t,
            None => {
                let available_cpus = available_parallelism()
                    .with_context(|| "Cannot gather available CPUs")?
                    .into();
                ThreadPoolBuilder::new()
                    .num_threads(available_cpus)
                    .build()
                    .with_context(|| {
                        format!("Cannot build thread pool with {available_cpus} threads")
                    })?
            }
        };

        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.info(format_args!(
            "Using {} threads.",
            threads.current_num_threads()
        ));
        pl.start("Visiting graph with ParallelExclusive Parallel BFV...");

        loop {
            current_frontier.clear();
            current_frontier.append(next_frontier_ref.lock().unwrap().as_mut());
            if current_frontier.is_empty() {
                let mut visited = visited_ref.lock().unwrap();
                while visited[start] {
                    start += 1;
                    if start >= visited.len() {
                        break;
                    }
                }
                if start >= visited.len() {
                    break;
                }
                visited.set(start, true);
                current_frontier.push(start);
            }

            let number_of_nodes = current_frontier.len();

            if number_of_nodes > 1 {
                threads.install(|| {
                    current_frontier
                        .as_mut_slice()
                        .par_chunks(threads.current_num_threads())
                        .for_each(|chunk| {
                            if chunk.is_empty() {
                                return;
                            }
                            let result_ref = result.clone();
                            let visited_vec = visited_ref.clone();
                            let next_frontier_vec = next_frontier_ref.clone();
                            let graph = self.graph;
                            let factory = self.node_factory;

                            join(
                                || {
                                    let mut results = Vec::new();
                                    for node_index in chunk {
                                        results.push(factory.node_from_index(*node_index).visit());
                                    }
                                    {
                                        let mut result_mutex = result_ref.lock().unwrap();
                                        for r in results {
                                            N::accumulate_result(&mut result_mutex, r);
                                        }
                                    }
                                },
                                || {
                                    let mut successors = Vec::new();
                                    for node_index in chunk {
                                        let mut succs: Vec<_> =
                                            graph.successors(*node_index).into_iter().collect();
                                        successors.append(&mut succs);
                                    }
                                    let mut to_add = Vec::new();
                                    {
                                        let mut visited = visited_vec.lock().unwrap();
                                        for succ in successors {
                                            if !visited[succ] {
                                                visited.set(succ, true);
                                                to_add.push(succ);
                                            }
                                        }
                                    }
                                    next_frontier_vec.lock().unwrap().append(&mut to_add);
                                },
                            );
                        });
                });
                pl.update_with_count(number_of_nodes);
            } else {
                let node = current_frontier.pop().unwrap();
                let mut visited = visited_ref.lock().unwrap();
                let mut next_frontier = next_frontier_ref.lock().unwrap();
                let mut res = result.lock().unwrap();
                N::accumulate_result(&mut res, self.node_factory.node_from_index(node).visit());
                for succ in self.graph.successors(node) {
                    if !visited[succ] {
                        visited.set(succ, true);
                        next_frontier.push(succ);
                    }
                }
                pl.light_update();
            }
        }

        pl.done();

        Ok(Arc::into_inner(result).unwrap().into_inner().unwrap())
    }
}
