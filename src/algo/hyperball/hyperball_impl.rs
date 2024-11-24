use crate::utils::traits::CounterMut;
use crate::{prelude::*, utils::*};
use anyhow::{bail, ensure, Context, Result};
use common_traits::Number;
use dsi_progress_logger::ProgressLog;
use kahan::KahanSum;
use rand::random;
use rayon::{prelude::*, ThreadPool};
use std::sync::{atomic::*, Mutex};
use sux::{bits::AtomicBitVec, traits::Succ};
use webgraph::traits::RandomAccessGraph;

/// Builder for [`HyperBall`].
///
/// Create a builder with [`HyperBallBuilder::new`], edit parameters with
/// its methods, then call [`HyperBallBuilder::build`] on it to create
/// the [`HyperBall`] as a [`Result`].
pub struct HyperBallBuilder<
    'a,
    D: Succ<Input = usize, Output = usize>,
    L: CounterLogic<Item = G1::Label> + MergeCounterLogic,
    A: CounterArrayMut<L>,
    G1: RandomAccessGraph + Sync,
    G2: RandomAccessGraph + Sync = G1,
> {
    graph: &'a G1,
    rev_graph: Option<&'a G2>,
    cumulative_outdegree: &'a D,
    sum_of_distances: bool,
    sum_of_inverse_distances: bool,
    discount_functions: Vec<Box<dyn Fn(usize) -> f64 + Sync + 'a>>,
    granularity: usize,
    weights: Option<&'a [usize]>,
    bits: A,
    result_bits: A,
    _marker: std::marker::PhantomData<L>,
}

impl<
        'a,
        D: Succ<Input = usize, Output = usize>,
        G: RandomAccessGraph + Sync,
        L: CounterLogic<Item = G::Label> + MergeCounterLogic,
        A: CounterArrayMut<L>,
    > HyperBallBuilder<'a, D, L, A, G, G>
{
    /// Creates a new builder with default parameters.
    ///
    /// # Arguments
    /// * `graph`: the direct graph to analyze.
    /// * `cumulative_outdegree`: the degree cumulative function of the graph.
    pub fn new(graph: &'a G, cumulative_outdegree: &'a D, bits: A, result_bits: A) -> Self {
        Self {
            graph,
            rev_graph: None,
            cumulative_outdegree,
            sum_of_distances: false,
            sum_of_inverse_distances: false,
            discount_functions: Vec::new(),
            granularity: Self::DEFAULT_GRANULARITY,
            weights: None,
            bits,
            result_bits,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<
        'a,
        D: Succ<Input = usize, Output = usize>,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        L: CounterLogic<Item = G1::Label> + MergeCounterLogic,
        A: CounterArrayMut<L>,
    > HyperBallBuilder<'a, D, L, A, G1, G2>
{
    const DEFAULT_GRANULARITY: usize = 16 * 1024;

    /// Sets the transposed graph to be used in systolic iterations in [`HyperBall`].
    ///
    /// # Arguments
    /// * `transposed`: the new transposed graph. If [`None`] no transposed graph is used
    ///   and no systolic iterations will be performed by the built [`HyperBall`].
    pub fn with_transposed(
        graph: &'a G1,
        transposed: &'a G2,
        cumulative_outdegree: &'a D,
        bits: A,
        result_bits: A,
    ) -> Self {
        assert_eq!(
            transposed.num_nodes(),
            graph.num_nodes(),
            "transposed should have same number of nodes ({}). Got {}.",
            graph.num_nodes(),
            transposed.num_nodes()
        );
        assert_eq!(
            transposed.num_arcs(),
            graph.num_arcs(),
            "transposed should have the same number of arcs ({}). Got {}.",
            graph.num_arcs(),
            transposed.num_arcs()
        );
        debug_assert!(
            check_transposed(graph, transposed),
            "transposed should be the transposed of the direct graph"
        );
        Self {
            graph,
            rev_graph: Some(transposed),
            cumulative_outdegree,
            sum_of_distances: false,
            sum_of_inverse_distances: false,
            discount_functions: Vec::new(),
            granularity: Self::DEFAULT_GRANULARITY,
            weights: None,
            bits,
            result_bits,
            _marker: std::marker::PhantomData,
        }
    }

    /// Sets whether to compute the sum of distances.
    ///
    /// # Arguments
    /// * `do_sum_of_distances`: if `true` the sum of distances are computed.
    pub fn sum_of_distances(mut self, do_sum_of_distances: bool) -> Self {
        self.sum_of_distances = do_sum_of_distances;
        self
    }

    /// Sets whether to compute the sum of inverse distances.
    ///
    /// # Arguments
    /// * `do_sum_of_inverse_distances`: if `true` the sum of inverse distances are computed.
    pub fn sum_of_inverse_distances(mut self, do_sum_of_inverse_distances: bool) -> Self {
        self.sum_of_inverse_distances = do_sum_of_inverse_distances;
        self
    }

    /// Sets the base granularity used in the parallel phases of the iterations.
    ///
    /// # Arguments
    /// * `granularity`: the new granularity value.
    pub fn granularity(mut self, granularity: usize) -> Self {
        self.granularity = granularity;
        self
    }

    /// Sets the weights for the nodes of the graph.
    ///
    /// # Arguments
    /// * `weights`: the new weights to use. If [`None`] every node is assumed to be
    ///   of weight equal to 1.
    pub fn weights(mut self, weights: Option<&'a [usize]>) -> Self {
        if let Some(w) = weights {
            assert_eq!(w.len(), self.graph.num_nodes());
        }
        self.weights = weights;
        self
    }

    /// Adds a new discount function to compute during the iterations.
    ///
    /// # Arguments
    /// * `discount_function`: the discount function to add.
    pub fn discount_function(
        mut self,
        discount_function: impl Fn(usize) -> f64 + Sync + 'a,
    ) -> Self {
        self.discount_functions.push(Box::new(discount_function));
        self
    }

    /// Removes all custom discount functions.
    pub fn no_discount_function(mut self) -> Self {
        self.discount_functions.clear();
        self
    }
}

impl<
        'a,
        D: Succ<Input = usize, Output = usize>,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        L: CounterLogic<Item = G1::Label> + MergeCounterLogic + Sync,
        A: CounterArrayMut<L>,
    > HyperBallBuilder<'a, D, L, A, G1, G2>
{
    /// Builds the [`HyperBall`] instance with the specified [`HyperLogLogBuilder`] and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// * `pl`: A progress logger.
    #[allow(clippy::type_complexity)]
    pub fn build(self, pl: &mut impl ProgressLog) -> HyperBall<'a, G1, G2, D, L, A> {
        let num_nodes = self.graph.num_nodes();

        let sum_of_distances = if self.sum_of_distances {
            pl.info(format_args!("Initializing sum of distances"));
            Some(Mutex::new(vec![0.0; num_nodes]))
        } else {
            pl.info(format_args!("Skipping sum of distances"));
            None
        };
        let sum_of_inverse_distances = if self.sum_of_inverse_distances {
            pl.info(format_args!("Initializing sum of inverse distances"));
            Some(Mutex::new(vec![0.0; num_nodes]))
        } else {
            pl.info(format_args!("Skipping sum of inverse distances"));
            None
        };

        let mut discounted_centralities = Vec::new();
        pl.info(format_args!(
            "Initializing {} discount fuctions",
            self.discount_functions.len()
        ));
        for _ in self.discount_functions.iter() {
            discounted_centralities.push(Mutex::new(vec![0.0; num_nodes]));
        }

        pl.info(format_args!("Initializing bit vectors"));

        pl.info(format_args!("Initializing modified_counter bitvec"));
        let modified_counter = AtomicBitVec::new(num_nodes);

        pl.info(format_args!("Initializing modified_result_counter bitvec"));
        let modified_result_counter = AtomicBitVec::new(num_nodes);

        pl.info(format_args!("Initializing must_be_checked bitvec"));
        let must_be_checked = AtomicBitVec::new(num_nodes);

        pl.info(format_args!("Initializing next_must_be_checked bitvec"));
        let next_must_be_checked = AtomicBitVec::new(num_nodes);

        HyperBall {
            graph: self.graph,
            transposed: self.rev_graph,
            cumulative_outdegree: self.cumulative_outdegree,
            weight: self.weights,
            prev_state: self.bits,
            next_state: self.result_bits,
            iteration: 0,
            completed: false,
            systolic: false,
            local: false,
            pre_local: false,
            sum_of_distances,
            sum_of_inverse_distances,
            discount_functions: self.discount_functions,
            discounted_centralities,
            neighbourhood_function: Vec::new(),
            last: 0.0,
            current: Mutex::new(0.0),
            prev_modified: modified_counter,
            next_modified: modified_result_counter,
            local_checklist: Vec::new(),
            local_next_must_be_checked: Mutex::new(Vec::new()),
            must_be_checked,
            next_must_be_checked,
            relative_increment: 0.0,
            granularity: self.granularity,
            iteration_context: IterationContext::default(),
            _marker: std::marker::PhantomData,
        }
    }
}

/// Utility used as container for iteration context
struct IterationContext {
    granularity: usize,
    cursor: AtomicUsize,
    arc_balanced_cursor: Mutex<(usize, usize)>,
    visited_arcs: AtomicU64,
    modified_counters: AtomicU64,
}

impl IterationContext {
    /// Resets the iteration context
    fn reset(&mut self, granularity: usize) {
        self.granularity = granularity;
        self.cursor.store(0, Ordering::Relaxed);
        *self.arc_balanced_cursor.lock().unwrap() = (0, 0);
        self.visited_arcs.store(0, Ordering::Relaxed);
        self.modified_counters.store(0, Ordering::Relaxed);
    }
}

impl Default for IterationContext {
    fn default() -> Self {
        Self {
            granularity: 0,
            cursor: AtomicUsize::new(0),
            arc_balanced_cursor: Mutex::new((0, 0)),
            visited_arcs: AtomicU64::new(0),
            modified_counters: AtomicU64::new(0),
        }
    }
}

/// An algorithm that computes an approximation of the neighbourhood function, of the size of the reachable sets,
/// and of (discounted) positive geometric centralities of a graph.
pub struct HyperBall<
    'a,
    G1: RandomAccessGraph + Sync,
    G2: RandomAccessGraph + Sync,
    D: Succ<Input = usize, Output = usize>,
    L: MergeCounterLogic<Item = G1::Label> + Sync,
    A: CounterArrayMut<L>,
> {
    /// The graph to analyze.
    graph: &'a G1,
    /// The transpose of [`Self::graph`], if any.
    transposed: Option<&'a G2>,
    /// The cumulative list of outdegrees.
    cumulative_outdegree: &'a D,
    /// An optional slice of nonegative node weights.
    weight: Option<&'a [usize]>,
    /// The base number of nodes per task. TODO.
    granularity: usize,
    /// The previous state.
    prev_state: A,
    /// The next state.
    next_state: A,
    /// The current iteration.
    iteration: usize,
    /// `true` if the computation is over.
    completed: bool,
    /// `true` if we started a systolic computation.
    systolic: bool,
    /// `true` if we started a local computation.
    local: bool,
    /// `true` if we are preparing a local computation (systolic is `true` and less than 1% nodes were modified).
    pre_local: bool,
    /// The sum of the distances from every given node, if requested.
    sum_of_distances: Option<Mutex<Vec<f64>>>,
    /// The sum of inverse distances from each given node, if requested.
    sum_of_inverse_distances: Option<Mutex<Vec<f64>>>,
    /// A number of discounted centralities to be computed, possibly none.
    discount_functions: Vec<Box<dyn Fn(usize) -> f64 + Sync + 'a>>,
    /// The overall discount centrality for every [`Self::discount_functions`].
    discounted_centralities: Vec<Mutex<Vec<f64>>>,
    /// The neighbourhood fuction.
    neighbourhood_function: Vec<f64>,
    /// The value computed by the last iteration.
    last: f64,
    /// The value computed by the current iteration.
    current: Mutex<f64>,
    /// Whether each counter has been modified during the previous iteration.
    prev_modified: AtomicBitVec,
    /// Whether each counter has been modified during the current iteration.
    next_modified: AtomicBitVec,
    /// If [`Self::local`] is `true`, the sorted list of nodes that should be scanned.
    local_checklist: Vec<G1::Label>,
    /// If [`Self::pre_local`] is `true`, the set of nodes that should be scanned on the next iteration.
    local_next_must_be_checked: Mutex<Vec<G1::Label>>,
    /// Used in systolic iterations to keep track of nodes to check.
    must_be_checked: AtomicBitVec,
    /// Used in systolic iterations to keep track of nodes to check in the next iteration.
    next_must_be_checked: AtomicBitVec,
    /// The relative increment of the neighbourhood function for the last iteration.
    relative_increment: f64,
    /// Context used in a single iteration.
    iteration_context: IterationContext,
    _marker: std::marker::PhantomData<L>,
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        D: Succ<Input = usize, Output = usize> + Sync,
        L: MergeCounterLogic<Item = usize> + Sync,
        A: CounterArrayMut<L> + Sync,
    > HyperBall<'a, G1, G2, D, L, A>
where
    L::Backend: PartialEq,
{
    /// Runs HyperBall.
    ///
    /// # Arguments
    /// * `upper_bound`: an upper bound to the number of iterations.
    /// * `threshold`: a value that will be used to stop the computation by relative increment if the neighbourhood
    ///   function is being computed. If [`None`] the computation will stop when no counters are modified.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    pub fn run(
        &mut self,
        upper_bound: usize,
        threshold: Option<f64>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        let upper_bound = std::cmp::min(upper_bound, self.graph.num_nodes());

        self.init(thread_pool, pl)
            .with_context(|| "Could not initialize approximator")?;

        pl.item_name("iteration");
        pl.expected_updates(None);
        pl.start(format!(
            "Running Hyperball for a maximum of {} iterations and a threshold of {:?}",
            upper_bound, threshold
        ));

        for i in 0..upper_bound {
            self.iterate(thread_pool, &mut pl.clone())
                .with_context(|| format!("Could not perform iteration {}", i + 1))?;

            pl.update();

            if self.modified_counters() == 0 {
                pl.info(format_args!(
                    "Terminating appoximation after {} iteration(s) by stabilisation",
                    i + 1
                ));
                break;
            }

            if let Some(t) = threshold {
                if i > 3 && self.relative_increment < (1.0 + t) {
                    pl.info(format_args!("Terminating approximation after {} iteration(s) by relative bound on the neighbourhood function", i + 1));
                    break;
                }
            }
        }

        pl.done();

        Ok(())
    }

    /// Runs HyperBall until no counters are modified.
    ///
    /// # Arguments
    /// * `upper_bound`: an upper bound to the number of iterations.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    #[inline(always)]
    pub fn run_until_stable(
        &mut self,
        upper_bound: usize,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.run(upper_bound, None, thread_pool, pl)
            .with_context(|| "Could not complete run_until_stable")
    }

    /// Runs HyperBall until no counters are modified with no upper bound on the number of iterations.
    ///
    /// # Arguments
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    #[inline(always)]
    pub fn run_until_done(
        &mut self,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.run_until_stable(usize::MAX, thread_pool, pl)
            .with_context(|| "Could not complete run_until_done")
    }

    #[inline(always)]
    fn ensure_iteration(&self) -> Result<()> {
        ensure!(
            self.iteration > 0,
            "HyperBall was not run. Please call self.run(...) before accessing computed fields"
        );
        Ok(())
    }

    /// Returns the neighbourhood function computed by this instance.
    pub fn neighbourhood_function(&self) -> Result<Vec<f64>> {
        self.ensure_iteration()?;
        Ok(self.neighbourhood_function.clone())
    }

    /// Returns the sum of distances computed by this instance if requested.
    pub fn sum_of_distances(&self) -> Result<Vec<f64>> {
        self.ensure_iteration()?;
        if let Some(distances) = &self.sum_of_distances {
            // TODO these are COPIES
            Ok(distances.lock().unwrap().to_vec())
        } else {
            bail!("Sum of distances were not requested. Use builder.with_sum_of_distances(true) while building HyperBall to compute them")
        }
    }

    /// Returns the harmonic centralities (sum of inverse distances) computed by this instance if requested.
    pub fn harmonic_centralities(&self) -> Result<Vec<f64>> {
        self.ensure_iteration()?;
        if let Some(distances) = &self.sum_of_inverse_distances {
            Ok(distances.lock().unwrap().to_vec())
        } else {
            bail!("Sum of inverse distances were not requested. Use builder.with_sum_of_inverse_distances(true) while building HyperBall to compute them")
        }
    }

    /// Returns the discounted centralities of the specified index computed by this instance.
    ///
    /// # Arguments
    /// * `index`: the index of the requested discounted centrality.
    pub fn discounted_centrality(&self, index: usize) -> Result<Vec<f64>> {
        self.ensure_iteration()?;
        let d = self.discounted_centralities.get(index);
        if let Some(distaces) = d {
            Ok(distaces.lock().unwrap().to_vec())
        } else {
            bail!("Discount centrality of index {} does not exist", index)
        }
    }

    /// Computes and returns the closeness centralities from the sum of distances computed by this instance.
    pub fn closeness_cetrality(&self) -> Result<Vec<f64>> {
        self.ensure_iteration()?;
        if let Some(distances) = &self.sum_of_distances {
            Ok(distances
                .lock()
                .unwrap()
                .iter()
                .map(|&d| if d == 0.0 { 0.0 } else { d.recip() })
                .collect())
        } else {
            bail!("Sum of distances were not requested. Use builder.with_sum_of_distances(true) while building HyperBall to compute closeness centrality")
        }
    }

    /// Computes and returns the lin centralities from the sum of distances computed by this instance.
    ///
    /// Note that lin's index for isolated nodes is by (our) definition one (it's smaller than any other node).
    pub fn lin_centrality(&self) -> Result<Vec<f64>> {
        self.ensure_iteration()?;
        if let Some(distances) = &self.sum_of_distances {
            let logic = self.prev_state.logic();
            Ok(distances
                .lock()
                .unwrap()
                .iter()
                .enumerate()
                .map(|(node, &d)| {
                    if d == 0.0 {
                        1.0
                    } else {
                        let count = logic.count(self.prev_state.get_backend(node));
                        count * count / d
                    }
                })
                .collect())
        } else {
            bail!("Sum of distances were not requested. Use builder.with_sum_of_distances(true) while building HyperBall to compute lin centrality")
        }
    }

    /// Computes and returns the nieminen centralities from the sum of distances computed by this instance.
    pub fn nieminen_centrality(&self) -> Result<Vec<f64>> {
        self.ensure_iteration()?;
        if let Some(distances) = &self.sum_of_distances {
            let logic = self.prev_state.logic();
            Ok(distances
                .lock()
                .unwrap()
                .iter()
                .enumerate()
                .map(|(node, &d)| {
                    let count = logic.count(self.prev_state.get_backend(node));
                    (count * count) - d
                })
                .collect())
        } else {
            bail!("Sum of distances were not requested. Use builder.with_sum_of_distances(true) while building HyperBall to compute lin centrality")
        }
    }

    /// Reads from the internal [`HyperLogLogCounterArray`] and estimates the number of nodes reachable
    /// from the specified node.
    ///
    /// # Arguments
    /// * `node`: the index of the node to compute reachable nodes from.
    pub fn reachable_nodes_from(&self, node: usize) -> Result<f64> {
        self.ensure_iteration()?;
        Ok(self
            .prev_state
            .logic()
            .count(self.prev_state.get_backend(node)))
    }

    /// Reads from the internal [`HyperLogLogCounterArray`] and estimates the number of nodes reachable
    /// from every node of the graph.
    ///
    /// `hyperball.reachable_nodes().unwrap()[i]` is equal to `hyperball.reachable_nodes_from(i).unwrap()`.
    pub fn reachable_nodes(&self) -> Result<Vec<f64>> {
        self.ensure_iteration()?;
        let logic = self.prev_state.logic();
        Ok((0..self.graph.num_nodes())
            .map(|n| logic.count(self.prev_state.get_backend(n)))
            .collect())
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        D: Succ<Input = usize, Output = usize> + Sync,
        L: MergeCounterLogic<Item = G1::Label> + Sync,
        A: CounterArrayMut<L> + Sync,
    > HyperBall<'a, G1, G2, D, L, A>
{
    #[inline(always)]
    fn swap_arrays(&mut self) {
        std::mem::swap(&mut self.prev_state, &mut self.next_state);
        std::mem::swap(&mut self.prev_modified, &mut self.next_modified);
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        D: Succ<Input = usize, Output = usize> + Sync,
        L: CounterLogic<Item = usize> + MergeCounterLogic + Sync,
        A: CounterArrayMut<L> + Sync,
    > HyperBall<'a, G1, G2, D, L, A>
where
    L::Backend: PartialEq,
{
    /// Performs a new iteration of HyperBall.
    ///
    /// # Arguments
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    fn iterate(&mut self, thread_pool: &ThreadPool, pl: &mut impl ProgressLog) -> Result<()> {
        pl.info(format_args!("Performing iteration {}", self.iteration + 1));

        // Let us record whether the previous computation was systolic or local.
        let previous_was_systolic = self.systolic;
        let previous_was_local = self.local;

        // Record the number of modified counters and the number of nodes and arcs as u64
        let modified_counters = self.modified_counters();
        let num_nodes = self.graph.num_nodes() as u64;
        let num_arcs = self.graph.num_arcs();

        // If less than one fourth of the nodes have been modified, and we have the transpose,
        // it is time to pass to a systolic computation.
        self.systolic =
            self.transposed.is_some() && self.iteration > 0 && modified_counters < num_nodes / 4;

        // Non-systolic computations add up the value of all counter.
        // Systolic computations modify the last value by compensating for each modified counter.
        *self.current.lock().unwrap() = if self.systolic { self.last } else { 0.0 };

        // If we completed the last iteration in pre-local mode, we MUST run in local mode.
        self.local = self.pre_local;

        // We run in pre-local mode if we are systolic and few nodes where modified.
        self.pre_local =
            self.systolic && modified_counters < (num_nodes * num_nodes) / (num_arcs * 10);

        if self.systolic {
            pl.info(format_args!(
                "Starting systolic iteration (local: {}, pre_local: {})",
                self.local, self.pre_local
            ));
        } else {
            pl.info(format_args!("Starting standard iteration"));
        }

        pl.info(format_args!("Preparing modified_result_counter"));
        if previous_was_local {
            for &node in self.local_checklist.iter() {
                self.next_modified.set(node, false, Ordering::Relaxed);
            }
        } else {
            thread_pool.install(|| self.next_modified.fill(false, Ordering::Relaxed));
        }

        if self.local {
            pl.info(format_args!("Preparing local checklist"));
            // In case of a local computation, we convert the set of must-be-checked for the
            // next iteration into a check list.
            thread_pool.join(
                || self.local_checklist.clear(),
                || {
                    let mut local_next_must_be_checked =
                        self.local_next_must_be_checked.lock().unwrap();
                    local_next_must_be_checked.par_sort_unstable();
                    local_next_must_be_checked.dedup();
                },
            );
            std::mem::swap(
                &mut self.local_checklist,
                &mut self.local_next_must_be_checked.lock().unwrap(),
            );
        } else if self.systolic {
            pl.info(format_args!("Preparing systolic flags"));
            thread_pool.join(
                || {
                    // Systolic, non-local computations store the could-be-modified set implicitly into Self::next_must_be_checked.
                    self.next_must_be_checked.fill(false, Ordering::Relaxed);
                },
                || {
                    // If the previous computation wasn't systolic, we must assume that all registers could have changed.
                    if !previous_was_systolic {
                        self.must_be_checked.fill(true, Ordering::Relaxed);
                    }
                },
            );
        }

        let mut granularity = self.granularity;
        let num_threads = thread_pool.current_num_threads();

        if num_threads > 1 && !self.local {
            if self.iteration > 0 {
                granularity = f64::min(
                    std::cmp::max(1, self.graph.num_nodes() / num_threads) as f64,
                    granularity as f64
                        * (self.graph.num_nodes() as f64
                            / std::cmp::max(1, modified_counters) as f64),
                ) as usize;
            }
            pl.info(format_args!(
                "Adaptive granularity for this iteration: {}",
                granularity
            ));
        }

        self.iteration_context.reset(granularity);

        pl.item_name("arc");
        pl.expected_updates(if self.local {
            None
        } else {
            Some(self.graph.num_arcs() as usize)
        });
        pl.start("Starting parallel execution");

        thread_pool.broadcast(|c| self.parallel_task(c));

        pl.done_with_count(self.iteration_context.visited_arcs.load(Ordering::Relaxed) as usize);

        pl.info(format_args!(
            "Modified counters: {}/{} ({:.3}%)",
            self.modified_counters(),
            self.graph.num_nodes(),
            (self.modified_counters() as f64 / self.graph.num_nodes() as f64) * 100.0
        ));

        self.swap_arrays();
        if self.systolic {
            std::mem::swap(&mut self.must_be_checked, &mut self.next_must_be_checked);
        }

        let mut current_mut = self.current.lock().unwrap();
        self.last = *current_mut;
        // We enforce monotonicity. Non-monotonicity can only be caused
        // by approximation errors.
        let &last_output = self
            .neighbourhood_function
            .as_slice()
            .last()
            .expect("Should always have at least 1 element");
        if *current_mut < last_output {
            *current_mut = last_output;
        }
        self.relative_increment = *current_mut / last_output;

        pl.info(format_args!(
            "Pairs: {} ({}%)",
            *current_mut,
            (*current_mut * 100.0) / (num_nodes * num_nodes) as f64
        ));
        pl.info(format_args!(
            "Absolute increment: {}",
            *current_mut - last_output
        ));
        pl.info(format_args!(
            "Relative increment: {}",
            self.relative_increment
        ));

        self.neighbourhood_function.push(*current_mut);

        self.iteration += 1;

        Ok(())
    }

    /// The parallel operations to be performed each iteration.
    ///
    /// # Arguments:
    /// * `broadcast_context`: the context of the for the parallel task
    fn parallel_task(&self, _broadcast_context: rayon::BroadcastContext) {
        let node_granularity = self.iteration_context.granularity;
        let arc_granularity = ((self.graph.num_arcs() as f64 * node_granularity as f64)
            / self.graph.num_nodes() as f64)
            .ceil() as usize;
        let do_centrality = self.sum_of_distances.is_some()
            || self.sum_of_inverse_distances.is_some()
            || !self.discount_functions.is_empty();
        let node_upper_limit = if self.local {
            self.local_checklist.len()
        } else {
            self.graph.num_nodes()
        };
        let mut visited_arcs = 0;
        let mut modified_counters = 0;
        let arc_upper_limit = self.graph.num_arcs() as usize;

        // During standard iterations, cumulates the neighbourhood function for the nodes scanned
        // by this thread. During systolic iterations, cumulates the *increase* of the
        // neighbourhood function for the nodes scanned by this thread.
        let mut neighbourhood_function_delta = KahanSum::new_with_value(0.0);
        let mut helper = self.prev_state.logic().new_helper();
        let counter_logic = self.prev_state.logic();
        let mut next_counter = counter_logic.new_counter();

        loop {
            // Get work
            let (start, end) = if self.local {
                let start = std::cmp::min(
                    self.iteration_context
                        .cursor
                        .fetch_add(1, Ordering::Relaxed),
                    node_upper_limit,
                );
                let end = std::cmp::min(start + 1, node_upper_limit);
                (start, end)
            } else {
                let mut arc_balanced_cursor =
                    self.iteration_context.arc_balanced_cursor.lock().unwrap();
                let (mut next_node, mut next_arc) = *arc_balanced_cursor;
                if next_node >= node_upper_limit {
                    (node_upper_limit, node_upper_limit)
                } else {
                    let start = next_node;
                    let target = next_arc + arc_granularity;
                    if target >= arc_upper_limit {
                        next_node = node_upper_limit;
                    } else {
                        (next_node, next_arc) = self.cumulative_outdegree.succ(target).unwrap();
                    }
                    let end = next_node;
                    *arc_balanced_cursor = (next_node, next_arc);
                    (start, end)
                }
            };

            if start == node_upper_limit {
                break;
            }

            // Do work
            for i in start..end {
                let node = if self.local {
                    self.local_checklist[i]
                } else {
                    i
                };

                let prev_counter = self.prev_state.get_backend(node);

                // The three cases in which we enumerate successors:
                // 1) A non-systolic computation (we don't know anything, so we enumerate).
                // 2) A systolic, local computation (the node is by definition to be checked, as it comes from the local check list).
                // 3) A systolic, non-local computation in which the node should be checked.
                if !self.systolic || self.local || self.must_be_checked[node] {
                    next_counter.set(prev_counter);
                    let mut modified = false;
                    for succ in self.graph.successors(node) {
                        if succ != node && self.prev_modified[succ] {
                            visited_arcs += 1;
                            if !modified {
                                modified = true;
                            }
                            counter_logic.merge_with_helper(
                                next_counter.as_backend_mut(),
                                self.prev_state.get_backend(succ),
                                &mut helper,
                            );
                        }
                    }

                    let mut post = f64::NAN;
                    let modified_counter = if modified {
                        next_counter.as_backend() != prev_counter
                    } else {
                        false
                    };

                    // We need the counter value only if the iteration is standard (as we're going to
                    // compute the neighbourhood function cumulating actual values, and not deltas) or
                    // if the counter was actually modified (as we're going to cumulate the neighbourhood
                    // function delta, or at least some centrality).
                    if !self.systolic || modified_counter {
                        post = counter_logic.count(next_counter.as_backend())
                    }
                    if !self.systolic {
                        neighbourhood_function_delta += post;
                    }

                    if modified_counter && (self.systolic || do_centrality) {
                        let pre = counter_logic.count(prev_counter);
                        if self.systolic {
                            neighbourhood_function_delta += -pre;
                            neighbourhood_function_delta += post;
                        }

                        if do_centrality {
                            let delta = post - pre;
                            // Note that this code is executed only for distances > 0
                            if delta > 0.0 {
                                if let Some(distances) = &self.sum_of_distances {
                                    let new_value = delta * (self.iteration + 1) as f64;
                                    distances.lock().unwrap()[node] += new_value;
                                }
                                if let Some(distances) = &self.sum_of_inverse_distances {
                                    let new_value = delta / (self.iteration + 1) as f64;
                                    distances.lock().unwrap()[node] += new_value;
                                }
                                for (func, distances) in self
                                    .discount_functions
                                    .iter()
                                    .zip(self.discounted_centralities.iter())
                                {
                                    let new_value = delta * func(self.iteration + 1);
                                    distances.lock().unwrap()[node] += new_value;
                                }
                            }
                        }
                    }

                    if modified_counter {
                        // We keep track of modified counters in the result. Note that we must
                        // add the current node to the must-be-checked set for the next
                        // local iteration if it is modified, as it might need a copy to
                        // the result array at the next iteration.
                        if self.pre_local {
                            self.local_next_must_be_checked.lock().unwrap().push(node);
                        }
                        self.next_modified.set(node, true, Ordering::Relaxed);

                        if self.systolic {
                            debug_assert!(self.transposed.is_some());
                            // In systolic computations we must keep track of which counters must
                            // be checked on the next iteration. If we are preparing a local computation,
                            // we do this explicitly, by adding the predecessors of the current
                            // node to a set. Otherwise, we do this implicitly, by setting the
                            // corresponding entry in an array.
                            let rev_graph = self.transposed.expect("Should have transpose");
                            if self.pre_local {
                                let mut local_next_must_be_checked =
                                    self.local_next_must_be_checked.lock().unwrap();
                                for succ in rev_graph.successors(node) {
                                    local_next_must_be_checked.push(succ);
                                }
                            } else {
                                for succ in rev_graph.successors(node) {
                                    self.next_must_be_checked.set(succ, true, Ordering::Relaxed);
                                }
                            }
                        }

                        modified_counters += 1;
                    }

                    unsafe {
                        self.next_state.set(node, next_counter.as_backend());
                    }
                } else {
                    // Even if we cannot possibly have changed our value, still our copy
                    // in the result vector might need to be updated because it does not
                    // reflect our current value.
                    if self.prev_modified[node] {
                        unsafe {
                            self.next_state.set(node, prev_counter);
                        }
                    }
                }
            }
        }

        *self.current.lock().unwrap() += neighbourhood_function_delta.sum();
        self.iteration_context
            .visited_arcs
            .fetch_add(visited_arcs, Ordering::Relaxed);
        self.iteration_context
            .modified_counters
            .fetch_add(modified_counters, Ordering::Relaxed);
    }

    /// Returns the number of HyperLogLog counters that were modified by the last iteration.
    fn modified_counters(&self) -> u64 {
        self.iteration_context
            .modified_counters
            .load(Ordering::Relaxed)
    }

    /// Initializes the approximator.
    ///
    /// # Arguments
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    fn init(&mut self, thread_pool: &ThreadPool, pl: &mut impl ProgressLog) -> Result<()> {
        pl.start("Initializing approximator");
        pl.info(format_args!("Clearing all registers"));
        self.prev_state.clear();
        self.next_state.clear();

        pl.info(format_args!("Initializing registers"));
        if let Some(w) = &self.weight {
            pl.info(format_args!("Loading weights"));
            for (i, &node_weight) in w.iter().enumerate() {
                let mut counter = self.prev_state.get_counter_mut(i);
                for _ in 0..node_weight {
                    counter.add(&random());
                }
            }
        } else {
            (0..self.graph.num_nodes()).for_each(|i| {
                self.prev_state.get_counter_mut(i).add(i);
            });
        }

        self.iteration = 0;
        self.completed = false;
        self.systolic = false;
        self.local = false;
        self.pre_local = false;
        self.iteration_context.reset(self.granularity);

        pl.info(format_args!("Initializing distances"));
        if let Some(distances) = &self.sum_of_distances {
            distances.lock().unwrap().fill(f64::ZERO);
        }
        if let Some(distances) = &self.sum_of_inverse_distances {
            distances.lock().unwrap().fill(f64::ZERO);
        }
        pl.info(format_args!("Initializing centralities"));
        for centralities in self.discounted_centralities.iter() {
            centralities.lock().unwrap().fill(0.0);
        }

        self.last = self.graph.num_nodes() as f64;
        pl.info(format_args!("Initializing neighbourhood function"));
        self.neighbourhood_function.clear();
        self.neighbourhood_function.push(self.last);

        pl.info(format_args!("Initializing modified counters"));
        thread_pool.install(|| self.prev_modified.fill(true, Ordering::Relaxed));

        pl.done();

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::hash::{BuildHasherDefault, DefaultHasher};

    use super::*;
    use crate::threads;
    use dsi_progress_logger::no_logging;
    use epserde::deser::{Deserialize, Flags};
    use webgraph::{
        prelude::{BvGraph, DCF},
        traits::SequentialLabeling,
    };

    struct SeqHyperBall<'a, G: RandomAccessGraph> {
        graph: &'a G,
        bits: SliceCounterArray<
            HyperLogLog<G::Label, BuildHasherDefault<DefaultHasher>, usize>,
            usize,
        >,
        result_bits: SliceCounterArray<
            HyperLogLog<G::Label, BuildHasherDefault<DefaultHasher>, usize>,
            usize,
        >,
    }

    impl<'a, G: RandomAccessGraph> SeqHyperBall<'a, G> {
        fn init(&mut self) {
            for i in 0..self.graph.num_nodes() {
                self.bits.get_counter_mut(i).add(i);
            }
        }

        fn iterate(&mut self) {
            for i in 0..self.graph.num_nodes() {
                let mut counter = self.result_bits.get_counter_mut(i);
                counter.set(self.bits.get_backend(i));
                for succ in self.graph.successors(i) {
                    counter.merge(self.bits.get_backend(succ));
                }
            }
            std::mem::swap(&mut self.bits, &mut self.result_bits);
        }
    }

    #[test]
    fn test_cnr_2000() -> Result<()> {
        let basename = "tests/graphs/cnr-2000";

        let graph = BvGraph::with_basename(basename).load()?;
        let transpose = BvGraph::with_basename(basename.to_owned() + "-t").load()?;
        let cumulative = DCF::load_mmap(basename.to_owned() + ".dcf", Flags::empty())?;

        let num_nodes = graph.num_nodes();

        let hyper_log_log = HyperLogLogBuilder::new(num_nodes)
            .seed(42)
            .log_2_num_reg(6)
            .build()?;

        let seq_bits = hyper_log_log.new_array(num_nodes, TempMmapOptions::Default)?;
        let seq_result_bits = hyper_log_log.new_array(num_nodes, TempMmapOptions::Default)?;
        let par_bits = hyper_log_log.new_array(num_nodes, TempMmapOptions::Default)?;
        let par_result_bits = hyper_log_log.new_array(num_nodes, TempMmapOptions::Default)?;

        let mut hyperball = HyperBallBuilder::with_transposed(
            &graph,
            &transpose,
            cumulative.as_ref(),
            par_bits,
            par_result_bits,
        )
        .build(no_logging![]);
        let mut seq_hyperball = SeqHyperBall {
            bits: seq_bits,
            result_bits: seq_result_bits,
            graph: &graph,
        };

        let mut modified_counters = num_nodes as u64;
        let threads = threads![];
        hyperball.init(&threads, no_logging![])?;
        seq_hyperball.init();

        while modified_counters != 0 {
            hyperball.iterate(&threads, no_logging![])?;
            seq_hyperball.iterate();

            modified_counters = hyperball.modified_counters();

            assert_eq!(
                hyperball.next_state.as_slice(),
                seq_hyperball.result_bits.as_slice()
            );
            assert_eq!(
                hyperball.prev_state.as_slice(),
                seq_hyperball.bits.as_slice()
            );
        }

        Ok(())
    }
}
