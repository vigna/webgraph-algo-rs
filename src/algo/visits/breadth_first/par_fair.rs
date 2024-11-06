use crate::algo::visits::{breadth_first, ParVisit};
use dsi_progress_logger::ProgressLog;
use parallel_frontier::prelude::{Frontier, ParallelIterator};
use rayon::prelude::*;
use std::{borrow::Borrow, sync::atomic::Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// A parallel visit where at each iteration
/// the frontier is divided in chunks for the threads in order to call the callback and perform
/// the visit logic. In order to do so both the node and its parent must be enqued in the frontier.
pub struct ParallelBreadthFirstVisit<
    'a,
    E,
    G: RandomAccessGraph,
    T: Borrow<rayon::ThreadPool> = rayon::ThreadPool,
> {
    graph: &'a G,
    granularity: usize,
    visited: AtomicBitVec,
    threads: T,
    _phantom: std::marker::PhantomData<E>,
}

impl<'a, E, G: RandomAccessGraph> ParallelBreadthFirstVisit<'a, E, G, rayon::ThreadPool> {
    /// Creates parallel top-down visit.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
    pub fn new(graph: &'a G, granularity: usize) -> Self {
        Self::with_num_threads(graph, granularity, 0)
    }

    /// Creates a parallel top-down visit that uses the specified number of threads.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
    /// * `num_threads`: the number of threads to use.
    pub fn with_num_threads(graph: &'a G, granularity: usize, num_threads: usize) -> Self {
        let threads = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .unwrap_or_else(|_| panic!("Could not build threadpool with {} threads", num_threads));
        Self::with_threads(graph, granularity, threads)
    }
}

impl<'a, E, G: RandomAccessGraph, T: Borrow<rayon::ThreadPool>>
    ParallelBreadthFirstVisit<'a, E, G, T>
{
    /// Creates a parallel top-down visit that uses the specified threadpool.
    ///
    /// # Arguments
    /// * `graph`: an immutable reference to the graph to visit.
    /// * `granularity`: the number of nodes in each chunk of the frontier to explore per thread.
    ///   High granularity reduces overhead, but may lead to decreased performance on graphs with skewed outdegrees.
    /// * `threads`: the threadpool to use.
    pub fn with_threads(graph: &'a G, granularity: usize, threads: T) -> Self {
        Self {
            graph,
            granularity,
            visited: AtomicBitVec::new(graph.num_nodes()),
            threads,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<'a, E: Send, G: RandomAccessGraph + Sync, T: Borrow<rayon::ThreadPool>>
    ParVisit<breadth_first::Args, E> for ParallelBreadthFirstVisit<'a, E, G, T>
{
    fn visit_filtered<
        C: Fn(&breadth_first::Args) -> Result<(), E> + Sync,
        F: Fn(&breadth_first::Args) -> bool + Sync,
    >(
        &mut self,
        root: usize,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        let args = breadth_first::Args {
            curr: root,
            parent: root,
            root,
            distance: 0,
            event: breadth_first::Event::Unknown,
        };

        if self.visited.get(root, Ordering::Relaxed) || !filter(&args) {
            return Ok(());
        }

        // We do not provide a capacity in the hope of allocating dyinamically
        // space as the frontiers grow.
        let mut curr_frontier = Frontier::with_threads(self.threads.borrow(), None);
        let mut next_frontier = Frontier::with_threads(self.threads.borrow(), None);

        self.threads.borrow().install(|| {
            curr_frontier.push((root, root));
        });

        self.visited.set(root, true, Ordering::Relaxed);
        let mut distance = 0;

        while !curr_frontier.is_empty() {
            let distance_plus_one = distance + 1;
            self.threads.borrow().install(|| {
                curr_frontier
                    .par_iter()
                    .chunks(self.granularity)
                    .try_for_each(|chunk| {
                        chunk.into_iter().try_for_each(|&(curr, parent)| {
                            callback(&breadth_first::Args {
                                curr,
                                parent,
                                root,
                                distance,
                                event: breadth_first::Event::Unknown,
                            })?;
                            self.graph
                                .successors(curr)
                                .into_iter()
                                .try_for_each(|succ| {
                                    if filter(&breadth_first::Args {
                                        curr: succ,
                                        parent: curr,
                                        root,
                                        distance: distance_plus_one,
                                        event: breadth_first::Event::Unknown,
                                    }) {
                                        if !self.visited.swap(succ, true, Ordering::Relaxed) {
                                            next_frontier.push((succ, curr));
                                        } else {
                                            callback(&breadth_first::Args {
                                                curr: succ,
                                                parent: curr,
                                                root,
                                                distance: distance_plus_one,
                                                event: breadth_first::Event::Known,
                                            })?;
                                        }
                                    }

                                    Result::<(), E>::Ok(())
                                })?;

                            Result::<(), E>::Ok(())
                        })
                    })
            })?;
            pl.update_with_count(curr_frontier.len());
            distance += 1;
            // Swap the frontiers
            std::mem::swap(&mut curr_frontier, &mut next_frontier);
            // Clear the frontier we will fill in the next iteration
            next_frontier.clear();
        }

        Ok(())
    }

    fn visit_all_filtered<
        C: Fn(&breadth_first::Args) -> Result<(), E> + Sync,
        F: Fn(&breadth_first::Args) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<(), E> {
        for node in 0..self.graph.num_nodes() {
            self.visit_filtered(node, &callback, &filter, pl)?;
        }

        Ok(())
    }

    fn reset(&mut self) {
        self.visited.fill(false, Ordering::Relaxed);
    }
}
