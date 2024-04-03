use crate::prelude::*;
use anyhow::{Context, Ok, Result};
use dsi_progress_logger::ProgressLog;
use rayon::prelude::*;
use rayon::{ThreadPool, ThreadPoolBuilder};
use std::{
    marker::PhantomData,
    sync::{Arc, Mutex},
    thread::available_parallelism,
};
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

/// A parallel visit that guarantees BFV order.
///
/// The order of the nodes is not guaranteed to be the same as [crate::algo::bfv::SingleThreadedBreadthFirstVisit],
/// but is guaranteed to never visit a node of a distance `X+1` before having visited all the nodes at distance `X`.
pub struct ParallelAssociativeBreadthFirstVisit<
    'a,
    G: RandomAccessGraph,
    N: AssociativeNodeVisit,
    F: NodeFactory<Node = N>,
> {
    graph: &'a G,
    start: usize,
    node_factory: &'a F,
    thread_pool: Option<ThreadPool>,
    _node_type: PhantomData<N>,
}

impl<'a, G: RandomAccessGraph, N: AssociativeNodeVisit, F: NodeFactory<Node = N>>
    ParallelAssociativeBreadthFirstVisit<'a, G, N, F>
{
    fn build(
        graph: &'a G,
        start: usize,
        node_factory: &'a F,
        pool: Option<ThreadPool>,
    ) -> ParallelAssociativeBreadthFirstVisit<'a, G, N, F> {
        ParallelAssociativeBreadthFirstVisit {
            graph,
            start,
            node_factory,
            thread_pool: pool,
            _node_type: PhantomData,
        }
    }

    /// Constructs a parallel BFV for the provided graph starting from the node with the
    /// specified index using the provided node factory and thread pool.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `node_factory`: An immutable reference to the node factory that produces nodes to visit
    /// from their index.
    /// - `start`: The index of the node from which to start the visit.
    /// - `pool`: The thread pool to use to parallelize the visit.
    pub fn with_start_and_threads(
        graph: &'a G,
        node_factory: &'a F,
        start: usize,
        pool: ThreadPool,
    ) -> ParallelAssociativeBreadthFirstVisit<'a, G, N, F> {
        Self::build(graph, start, node_factory, Some(pool))
    }

    /// Constructs a parallel BFV for the provided graph using the provided node factory
    /// and thread pool.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `node_factory`: An immutable reference to the node factory that produces nodes to visit
    /// from their index.
    /// - `pool`: The thread pool to use to parallelize the visit.
    pub fn with_threads(
        graph: &'a G,
        node_factory: &'a F,
        pool: ThreadPool,
    ) -> ParallelAssociativeBreadthFirstVisit<'a, G, N, F> {
        Self::build(graph, 0, node_factory, Some(pool))
    }

    /// Constructs a parallel BFV starting from the node with the specified index in the
    /// provided graph using the provided node factory.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `node_factory`: An immutable reference to the node factory that produces nodes to visit
    /// from their index.
    /// - `start`: The index of the node from which to start the visit.
    pub fn with_start(
        graph: &'a G,
        node_factory: &'a F,
        start: usize,
    ) -> ParallelAssociativeBreadthFirstVisit<'a, G, N, F> {
        Self::build(graph, start, node_factory, None)
    }

    /// Constructs a parallel BFV for the specified graph using the provided node factory.
    ///
    /// # Arguments:
    /// - `graph`: An immutable reference to the graph to visit.
    /// - `node_factory`: An immutable reference to the node factory that produces nodes to visit
    /// from their index.
    pub fn new(
        graph: &'a G,
        node_factory: &'a F,
    ) -> ParallelAssociativeBreadthFirstVisit<'a, G, N, F> {
        Self::with_start(graph, node_factory, 0)
    }
}

impl<
        'a,
        G: RandomAccessGraph + Sync,
        R: Send,
        N: AssociativeNodeVisit<AccumulatedResult = R>,
        F: NodeFactory<Node = N> + Sync,
    > GraphVisit<N> for ParallelAssociativeBreadthFirstVisit<'a, G, N, F>
{
    fn visit(self, mut pl: impl ProgressLog) -> Result<N::AccumulatedResult> {
        let num_nodes = self.graph.num_nodes();
        let result = Arc::new(Mutex::new(N::init_result()));
        let visited_ref = Arc::new(Mutex::new(BitVec::new(self.graph.num_nodes())));
        let mut current_frontier = Vec::new();
        let next_frontier_ref = Arc::new(Mutex::new(Vec::new()));
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
        next_frontier_ref.lock().unwrap().push(self.start);
        visited_ref.lock().unwrap().set(self.start, true);

        pl.expected_updates(Some(num_nodes));
        pl.info(format_args!(
            "Using {} threads.",
            threads.current_num_threads()
        ));
        pl.start("Visiting graph with ParallelExclusive Parallel BFV...");

        loop {
            current_frontier.clear();
            current_frontier.append(&mut next_frontier_ref.lock().unwrap());
            if current_frontier.is_empty() {
                let visited_nodes = threads.install(|| {
                    let visited_vec = visited_ref.lock().unwrap();
                    let mut result_mutex = result.lock().unwrap();
                    let visits: Vec<_> = (0..num_nodes)
                        .into_par_iter()
                        .filter(|&index| !visited_vec[index])
                        .map(|index| self.node_factory.node_from_index(index).visit())
                        .collect();
                    let count = visits.len();
                    for visit_result in visits {
                        N::accumulate_result(&mut result_mutex, visit_result);
                    }
                    count
                });
                pl.update_with_count(visited_nodes);
                break;
            }

            let number_of_nodes = current_frontier.len();

            if number_of_nodes > 1 {
                let nodes_slice = current_frontier.as_slice();
                threads.join(
                    || {
                        let partial_result = nodes_slice
                            .par_iter()
                            .fold(N::init_result, |mut acc, &elem| {
                                N::accumulate_result(
                                    &mut acc,
                                    self.node_factory.node_from_index(elem).visit(),
                                );
                                acc
                            })
                            .reduce(N::init_result, |mut acc, elem| {
                                N::merge_result(&mut acc, elem);
                                acc
                            });
                        {
                            let mut result_mutex = result.lock().unwrap();
                            N::merge_result(&mut result_mutex, partial_result);
                        }
                    },
                    || {
                        nodes_slice
                            .par_iter()
                            .fold(Vec::new, |mut acc, &elem| {
                                acc.append(&mut Vec::from_iter(self.graph.successors(elem)));
                                acc
                            })
                            .for_each(|elem| {
                                let mut to_add = Vec::with_capacity(elem.len());
                                {
                                    let mut visited = visited_ref.lock().unwrap();
                                    for succ in elem {
                                        if !visited[succ] {
                                            visited.set(succ, true);
                                            to_add.push(succ);
                                        }
                                    }
                                }
                                next_frontier_ref.lock().unwrap().append(&mut to_add);
                            });
                    },
                );
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

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Context;
    use webgraph::graphs::BVGraph;

    struct Node {
        index: usize,
    }

    struct Factory {}

    impl NodeVisit for Node {
        type VisitResult = usize;
        type AccumulatedResult = Vec<usize>;

        fn init_result() -> Self::AccumulatedResult {
            Vec::new()
        }

        fn accumulate_result(
            partial_result: &mut Self::AccumulatedResult,
            visit_result: Self::VisitResult,
        ) {
            partial_result.push(visit_result)
        }

        fn visit(self) -> Self::VisitResult {
            self.index
        }
    }

    impl AssociativeNodeVisit for Node {
        fn merge_result(
            accumulated_result: &mut Self::AccumulatedResult,
            mut partial_result: Self::AccumulatedResult,
        ) {
            accumulated_result.append(&mut partial_result)
        }
    }

    impl NodeFactory for Factory {
        type Node = Node;

        fn node_from_index(&self, node_index: usize) -> Self::Node {
            Node { index: node_index }
        }
    }

    #[test]
    fn test_parallel_bfv_with_start() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let factory = Factory {};
        let visit = ParallelAssociativeBreadthFirstVisit::with_start(&graph, &factory, 10);

        assert_eq!(visit.start, 10);
        assert!(visit.thread_pool.is_none());

        Ok(())
    }

    #[test]
    fn test_parallel_bfv_new() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let factory = Factory {};
        let visit = ParallelAssociativeBreadthFirstVisit::new(&graph, &factory);

        assert_eq!(visit.start, 0);
        assert!(visit.thread_pool.is_none());

        Ok(())
    }

    #[test]
    fn test_parallel_bfv_with_threads() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let factory = Factory {};
        let threads = ThreadPoolBuilder::default().build()?;
        let visit = ParallelAssociativeBreadthFirstVisit::with_threads(&graph, &factory, threads);

        assert_eq!(visit.start, 0);
        assert!(visit.thread_pool.is_some());

        Ok(())
    }

    #[test]
    fn test_parallel_bfv_with_start_and_threads() -> Result<()> {
        let graph = BVGraph::with_basename("tests/graphs/cnr-2000")
            .load()
            .with_context(|| "Cannot load graph")?;
        let factory = Factory {};
        let threads = ThreadPoolBuilder::default().build()?;
        let visit = ParallelAssociativeBreadthFirstVisit::with_start_and_threads(
            &graph, &factory, 150, threads,
        );

        assert_eq!(visit.start, 150);
        assert!(visit.thread_pool.is_some());

        Ok(())
    }
}
