use crate::{
    algo::hyperball::kahan_sum::KahanSummation,
    prelude::*,
    utils::{HyperLogLogCounter, HyperLogLogCounterArray, HyperLogLogCounterArrayBuilder},
};
use anyhow::{Context, Result};
use common_traits::{AsBytes, AtomicUnsignedInt, IntoAtomic, Number, UpcastableInto};
use dsi_progress_logger::ProgressLog;
use rand::random;
use rayon::prelude::*;
use std::{
    hash::{BuildHasher, BuildHasherDefault, DefaultHasher},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Mutex,
    },
};
use sux::{
    bits::AtomicBitVec,
    traits::{BitCount, Succ, Word},
};
use webgraph::traits::RandomAccessGraph;

/// Builder for [`HyperBall`].
///
/// Create a builder with [`HyperBallBuilder::new`], edit parameters with
/// its methods, then call [`HyperBallBuilder::build`] on it to create
/// the [`HyperBall`] as a [`Result`].
pub struct HyperBallBuilder<
    'a,
    D: Succ<Input = usize, Output = usize>,
    W: Word + IntoAtomic,
    H: BuildHasher,
    G1: RandomAccessGraph,
    G2: RandomAccessGraph = G1,
> {
    graph: &'a G1,
    rev_graph: Option<&'a G2>,
    cumulative_outdegree: &'a D,
    neighbourhood_function: bool,
    sum_of_distances: bool,
    sum_of_inverse_distances: bool,
    discount_functions: Vec<Box<dyn Fn(usize) -> f64 + Sync + 'a>>,
    granularity: usize,
    weights: Option<&'a [usize]>,
    hyper_log_log_settings: HyperLogLogCounterArrayBuilder<H, W>,
}

impl<'a, D: Succ<Input = usize, Output = usize>, G: RandomAccessGraph>
    HyperBallBuilder<'a, D, usize, BuildHasherDefault<DefaultHasher>, G>
{
    const DEFAULT_GRANULARITY: usize = 16 * 1024;

    /// Creates a new builder with default parameters.
    ///
    /// # Arguments
    /// - `graph`: the direct graph to analyze.
    /// - `cumulative_outdegree`: the degree cumulative function of the graph.
    pub fn new(graph: &'a G, cumulative_outdegree: &'a D) -> Self {
        let hyper_log_log_settings = HyperLogLogCounterArrayBuilder::new_with_word_type()
            .with_num_elements_upper_bound(graph.num_nodes())
            .with_mem_options(TempMmapOptions::None);
        Self {
            graph,
            rev_graph: None,
            cumulative_outdegree,
            neighbourhood_function: false,
            sum_of_distances: false,
            sum_of_inverse_distances: false,
            discount_functions: Vec::new(),
            granularity: Self::DEFAULT_GRANULARITY,
            weights: None,
            hyper_log_log_settings,
        }
    }
}

impl<
        'a,
        D: Succ<Input = usize, Output = usize>,
        W: Word + IntoAtomic,
        H: BuildHasher,
        G1: RandomAccessGraph,
        G2: RandomAccessGraph,
    > HyperBallBuilder<'a, D, W, H, G1, G2>
{
    /// Sets the transposed graph to be used in systolic iterations in [`HyperBall`].
    ///
    /// # Arguments
    /// - `transposed`: the new transposed graph. If [`None`] no transposed graph is used
    ///   and no systolic iterations will be performed by the built [`HyperBall`].
    pub fn with_transposed<G: RandomAccessGraph>(
        self,
        transposed: Option<&'a G>,
    ) -> HyperBallBuilder<'a, D, W, H, G1, G> {
        if let Some(t) = transposed {
            assert_eq!(t.num_nodes(), self.graph.num_nodes());
            assert_eq!(t.num_arcs(), self.graph.num_arcs());
        }
        HyperBallBuilder {
            graph: self.graph,
            rev_graph: transposed,
            cumulative_outdegree: self.cumulative_outdegree,
            neighbourhood_function: self.neighbourhood_function,
            sum_of_distances: self.sum_of_distances,
            sum_of_inverse_distances: self.sum_of_inverse_distances,
            discount_functions: self.discount_functions,
            granularity: self.granularity,
            weights: self.weights,
            hyper_log_log_settings: self.hyper_log_log_settings,
        }
    }

    /// Sets whether to compute the sum of distances.
    ///
    /// # Arguments
    /// - `do_sum_of_distances`: if `true` the sum of distances are computed.
    pub fn with_sum_of_distances(mut self, do_sum_of_distances: bool) -> Self {
        self.sum_of_distances = do_sum_of_distances;
        self
    }

    /// Sets whether to compute the sum of inverse distances.
    ///
    /// # Arguments
    /// - `do_sum_of_inverse_distances`: if `true` the sum of inverse distances are computed.
    pub fn with_sum_of_inverse_distances(mut self, do_sum_of_inverse_distances: bool) -> Self {
        self.sum_of_inverse_distances = do_sum_of_inverse_distances;
        self
    }

    /// Sets whether to compute the neighbourhood function.
    ///
    /// # Arguments
    /// - `do_neighbourhood_function`: if `true` the neighbourhood function is computed.
    pub fn with_neighbourhood_function(mut self, do_neighbourhood_function: bool) -> Self {
        self.neighbourhood_function = do_neighbourhood_function;
        self
    }

    /// Sets the base granularity used in the parallel phases of the iterations.
    ///
    /// # Arguments
    /// - `granularity`: the new granularity value.
    pub fn with_granularity(mut self, granularity: usize) -> Self {
        self.granularity = granularity;
        self
    }

    /// Sets the weights for the nodes of the graph.
    ///
    /// # Arguments
    /// - `weights`: the new weights to use. If [`None`] every node is assumed to be
    ///   of weight equal to 1.
    pub fn with_weights(mut self, weights: Option<&'a [usize]>) -> Self {
        if let Some(w) = weights {
            assert_eq!(w.len(), self.graph.num_nodes());
        }
        self.weights = weights;
        self
    }

    /// Adds a new discount function to compute during the iterations.
    ///
    /// # Arguments
    /// - `discount_function`: the discount function to add.
    pub fn with_discount_function<F: Fn(usize) -> f64 + Sync>(
        mut self,
        discount_function: impl Fn(usize) -> f64 + Sync + 'a,
    ) -> Self {
        self.discount_functions.push(Box::new(discount_function));
        self
    }

    /// Removes all custom discount functions.
    pub fn with_no_discount_function(mut self) -> Self {
        self.discount_functions.clear();
        self
    }

    /// Sets the settings for the [`HyperLogLogCounterArray`] used to hold the counters.
    ///
    /// # Arguments
    /// - `settings`: the new settings to use.
    pub fn with_hyperloglog_settings<W2: Word + IntoAtomic, H2: BuildHasher>(
        self,
        settings: HyperLogLogCounterArrayBuilder<H2, W2>,
    ) -> HyperBallBuilder<'a, D, W2, H2, G1, G2> {
        HyperBallBuilder {
            graph: self.graph,
            rev_graph: self.rev_graph,
            cumulative_outdegree: self.cumulative_outdegree,
            neighbourhood_function: self.neighbourhood_function,
            sum_of_distances: self.sum_of_distances,
            sum_of_inverse_distances: self.sum_of_inverse_distances,
            discount_functions: self.discount_functions,
            granularity: self.granularity,
            weights: self.weights,
            hyper_log_log_settings: settings,
        }
    }
}

impl<
        'a,
        D: Succ<Input = usize, Output = usize>,
        W: Word + IntoAtomic,
        H: BuildHasher + Clone,
        G1: RandomAccessGraph,
        G2: RandomAccessGraph,
    > HyperBallBuilder<'a, D, W, H, G1, G2>
{
    /// Builds the [`HyperBall`] instance with the specified settings and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    pub fn build(self, pl: impl ProgressLog) -> Result<HyperBall<'a, G1, G2, D, W, H>> {
        let num_nodes = self.graph.num_nodes();

        let bits = self
            .hyper_log_log_settings
            .clone()
            .build(num_nodes)
            .with_context(|| "Could not initialize bits")?;
        let result_bits = self
            .hyper_log_log_settings
            .build(num_nodes)
            .with_context(|| "Could not initialize result_bits")?;

        let sum_of_distances = if self.sum_of_distances {
            Some(Mutex::new(vec![0.0; num_nodes]))
        } else {
            None
        };
        let sum_of_inverse_distances = if self.sum_of_inverse_distances {
            Some(Mutex::new(vec![0.0; num_nodes]))
        } else {
            None
        };
        let neighbourhood_function = if self.neighbourhood_function {
            Some(Vec::new())
        } else {
            None
        };

        let mut discounted_centralities = Vec::new();
        for _ in self.discount_functions.iter() {
            discounted_centralities.push(Mutex::new(vec![0.0; num_nodes]));
        }

        let granularity = (self.granularity + W::BITS - 1) & W::BITS.wrapping_neg();

        pl.info(format_args!(
            "Relative standard deviation: {}% ({} registers/counter, {} bits/register, {} bytes/counter)",
            100.0 * HyperLogLogCounterArray::relative_standard_deviation(bits.log_2_num_registers()),
            bits.num_registers(),
            bits.register_size(),
            (bits.num_registers() * bits.register_size()) / 8
        ));

        Ok(HyperBall {
            graph: self.graph,
            rev_graph: self.rev_graph,
            cumulative_outdegree: self.cumulative_outdegree,
            weight: self.weights,
            bits,
            result_bits,
            iteration: 0,
            completed: false,
            systolic: false,
            local: false,
            pre_local: false,
            sum_of_distances,
            sum_of_inverse_distances,
            discount_functions: self.discount_functions,
            discounted_centralities,
            neighbourhood_function,
            last: 0.0,
            current: Mutex::new(0.0),
            modified_counter: AtomicBitVec::new(num_nodes),
            modified_result_counter: AtomicBitVec::new(num_nodes),
            local_checklist: Vec::new(),
            local_next_must_be_checked: Mutex::new(Vec::new()),
            must_be_checked: AtomicBitVec::new(num_nodes),
            next_must_be_checked: AtomicBitVec::new(num_nodes),
            relative_increment: 0.0,
            granularity,
        })
    }
}

struct ParallelContext<'a, 'b> {
    #[allow(dead_code)]
    rayon_context: rayon::BroadcastContext<'a>,
    granularity: usize,
    cursor: &'b AtomicUsize,
}

pub struct HyperBall<
    'a,
    G1: RandomAccessGraph,
    G2: RandomAccessGraph,
    D: Succ<Input = usize, Output = usize>,
    W: Word + IntoAtomic = usize,
    H: BuildHasher = BuildHasherDefault<DefaultHasher>,
> {
    /// The direct graph to analyze
    graph: &'a G1,
    /// The transposed of the graph to analyze
    rev_graph: Option<&'a G2>,
    /// The cumulative list of outdegrees
    cumulative_outdegree: &'a D,
    /// A slice of nonegative node weights
    weight: Option<&'a [usize]>,
    /// The current status of Hyperball
    bits: HyperLogLogCounterArray<G1::Label, W, H>,
    /// The new status of Hyperball after an iteration
    result_bits: HyperLogLogCounterArray<G1::Label, W, H>,
    /// The current iteration
    iteration: usize,
    /// `true` if the computation is over
    completed: bool,
    /// `true` if we started a systolic computation
    systolic: bool,
    /// `true` if we started a local computation
    local: bool,
    /// `true` if we are preparing a local computation (systolic is `true` and less than 1% nodes were modified)
    pre_local: bool,
    /// The sum of the distances from every give node, if requested
    sum_of_distances: Option<Mutex<Vec<f64>>>,
    /// The sum of inverse distances from each given node, if requested
    sum_of_inverse_distances: Option<Mutex<Vec<f64>>>,
    /// A number of discounted centralities to be computed, possibly none
    discount_functions: Vec<Box<dyn Fn(usize) -> f64 + Sync + 'a>>,
    /// The overall discount centrality for every [`Self::discount_functions`]
    discounted_centralities: Vec<Mutex<Vec<f64>>>,
    /// The neighbourhood fuction if requested
    neighbourhood_function: Option<Vec<f64>>,
    /// The value computed by the last iteration
    last: f64,
    /// The value computed by the current iteration
    current: Mutex<f64>,
    /// `modified_counter[i]` is `true` if `bits.get_counter(i)` has been modified
    modified_counter: AtomicBitVec,
    /// `modified_result_counter[i]` is `true` if `result_bits.get_counter(i)` has been modified
    modified_result_counter: AtomicBitVec,
    /// If [`Self::local`] is `true`, the sorted list of nodes that should be scanned
    local_checklist: Vec<usize>,
    /// If [`Self::pre_local`] is `true`, the set of nodes that should be scanned on the next iteration
    local_next_must_be_checked: Mutex<Vec<usize>>,
    /// Used in systolic iterations to keep track of nodes to check
    must_be_checked: AtomicBitVec,
    /// Used in systolic iterations to keep track of nodes to check in the next iteration
    next_must_be_checked: AtomicBitVec,
    /// The relative increment of the neighbourhood function for the last iteration
    relative_increment: f64,
    /// The base number of nodes per task. Must be a multiple of `bits.chuk_size()`
    granularity: usize,
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        D: Succ<Input = usize, Output = usize> + Sync,
        W: Word + TryFrom<u64> + UpcastableInto<u64> + IntoAtomic,
        H: BuildHasher + Sync,
    > HyperBall<'a, G1, G2, D, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    /// Runs HyperBall.
    ///
    /// # Arguments
    /// - `upper_bound`: an upper bound to the number of iterations.
    /// - `threshold`: a value that will be used to stop the computation by relative increment if the neighbourhood
    ///   function is being computed. If [`None`] the computation will stop when no counters are modified.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    pub fn run(
        &mut self,
        upper_bound: usize,
        threshold: Option<f64>,
        mut pl: impl ProgressLog,
    ) -> Result<()> {
        let upper_bound = std::cmp::min(upper_bound, self.graph.num_nodes());

        self.init(pl.clone())
            .with_context(|| "Could not initialize approximator")?;

        pl.item_name("iteration(s)");
        pl.expected_updates(None);
        pl.start(format!(
            "Running Hyperball for a maximum of {} iterations and a threshold of {:?}",
            upper_bound, threshold
        ));

        for i in 0..upper_bound {
            self.iterate(pl.clone())
                .with_context(|| format!("Could not perform iteration {}", i))?;

            pl.update();

            if self.modified_counters() == 0 {
                pl.info(format_args!(
                    "Terminating appoximation after {} iteration(s) by stabilisation",
                    i
                ));
                break;
            }

            if let Some(t) = threshold {
                if i > 3 && self.relative_increment < (1.0 + t) {
                    pl.info(format_args!("Terminating approximation after {} iteration(s) by relative bound on the neighbourhood function", i));
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
    /// - `upper_bound`: an upper bound to the number of iterations.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    #[inline(always)]
    pub fn run_until_stable(&mut self, upper_bound: usize, pl: impl ProgressLog) -> Result<()> {
        self.run(upper_bound, None, pl)
            .with_context(|| "Could not complete run_until_stable")
    }

    /// Runs HyperBall until no counters are modified with no upper bound on the number of iterations.
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    #[inline(always)]
    pub fn run_until_done(&mut self, pl: impl ProgressLog) -> Result<()> {
        self.run_until_stable(usize::MAX, pl)
            .with_context(|| "Could not complete run_until_done")
    }
}

impl<
        'a,
        G1: RandomAccessGraph,
        G2: RandomAccessGraph,
        D: Succ<Input = usize, Output = usize> + Sync,
        W: Word + IntoAtomic,
        H: BuildHasher,
    > HyperBall<'a, G1, G2, D, W, H>
{
    /// Swaps the undelying backend [`HyperLogLogCounterArray`] between current and result.
    #[inline(always)]
    fn swap_backend(&mut self) {
        self.bits.swap_with(&mut self.result_bits);
        std::mem::swap(
            &mut self.modified_counter,
            &mut self.modified_result_counter,
        );
    }

    /// Returns the counter of the specified index using as backend [`Self::current`].
    #[inline(always)]
    fn get_current_counter(&self, index: usize) -> HyperLogLogCounter<G1::Label, W, H> {
        self.bits.get_counter(index)
    }

    /// Returns the counter of the specified index using as backend [`Self::result`].
    #[inline(always)]
    fn get_result_counter(&self, index: usize) -> HyperLogLogCounter<G1::Label, W, H> {
        self.result_bits.get_counter(index)
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        D: Succ<Input = usize, Output = usize> + Sync,
        W: Word + TryFrom<u64> + UpcastableInto<u64> + IntoAtomic,
        H: BuildHasher + Sync,
    > HyperBall<'a, G1, G2, D, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    /// Performs a new iteration of HyperBall.
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn iterate(&mut self, pl: impl ProgressLog) -> Result<()> {
        pl.info(format_args!("Performing iteration {}", self.iteration));

        // Let us record whether the previous computation was systolic or local.
        let previous_was_systolic = self.systolic;
        let previous_was_local = self.local;

        // Record the number of modified counters and the number of nodes and arcs as u64
        let modified_counters: u64 = self
            .modified_counters()
            .try_into()
            .with_context(|| format!("Could not convert {} into u64", self.modified_counters()))?;
        let num_nodes: u64 =
            self.graph.num_nodes().try_into().with_context(|| {
                format!("Could not convert {} into u64", self.graph.num_nodes())
            })?;
        let num_arcs: u64 = self.graph.num_arcs();

        // If less than one fourth of the nodes have been modified, and we have the transpose,
        // it is time to pass to a systolic computation.
        self.systolic =
            self.rev_graph.is_some() && self.iteration > 0 && modified_counters < num_nodes / 4;

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
                self.modified_result_counter
                    .set(node, false, Ordering::Relaxed);
            }
        } else {
            self.modified_result_counter.fill(false, Ordering::Relaxed);
        }

        if self.local {
            pl.info(format_args!("Preparing local checklist"));
            // In case of a local computation, we convert the set of must-be-checked for the
            // next iteration into a check list.
            let mut local_next_must_be_checked = self.local_next_must_be_checked.lock().unwrap();
            local_next_must_be_checked.par_sort_unstable();
            local_next_must_be_checked.dedup();
            self.local_checklist.clear();
            std::mem::swap(&mut self.local_checklist, &mut local_next_must_be_checked);
        } else if self.systolic {
            pl.info(format_args!("Preparing systolic flags"));
            // Systolic, non-local computations store the could-be-modified set implicitly into Self::next_must_be_checked.
            self.next_must_be_checked.fill(false, Ordering::Relaxed);

            // If the previous computation wasn't systolic, we must assume that all registers could have changed.
            if !previous_was_systolic {
                self.must_be_checked.fill(true, Ordering::Relaxed);
            }
        }

        let mut granularity = self.granularity;
        let num_threads = rayon::current_num_threads();

        if num_threads > 1 && !self.local {
            if self.iteration > 0 {
                granularity = f64::min(
                    std::cmp::max(1, self.graph.num_nodes() / num_threads) as f64,
                    granularity as f64
                        * (self.graph.num_nodes() as f64
                            / std::cmp::max(1, self.modified_counters()) as f64),
                ) as usize;
                granularity = (granularity + W::BITS - 1) & W::BITS.wrapping_neg();
            }
            pl.info(format_args!(
                "Adaptive granularity for this iteration: {}",
                granularity
            ));
        }

        let cursor = AtomicUsize::new(0);

        rayon::broadcast(|c| {
            self.parallel_task(ParallelContext {
                rayon_context: c,
                granularity,
                cursor: &cursor,
            })
        });

        self.swap_backend();
        if self.systolic {
            std::mem::swap(&mut self.must_be_checked, &mut self.next_must_be_checked);
        }

        let mut current_mut = self.current.lock().unwrap();
        self.last = *current_mut;
        // We enforce monotonicity. Non-monotonicity can only be caused
        // by approximation errors.
        if let Some(n_function) = &mut self.neighbourhood_function {
            let &last_output = n_function
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

            n_function.push(*current_mut);
        }

        self.iteration += 1;

        Ok(())
    }

    /// The parallel operations to be performed each iteration.
    ///
    /// # Arguments:
    /// - `broadcast_context`: the context of the rayon::broadcast function
    fn parallel_task(&self, context: ParallelContext) {
        let node_granularity = if self.local { 1 } else { context.granularity };
        /*let arc_granularity = ((self.graph.num_arcs() as f64 * node_granularity as f64)
        / self.graph.num_nodes() as f64)
        .ceil() as usize;*/
        let do_centrality = self.sum_of_distances.is_some()
            || self.sum_of_inverse_distances.is_some()
            || !self.discount_functions.is_empty();
        let upper_limit = if self.local {
            self.local_checklist.len()
        } else {
            self.graph.num_nodes()
        };
        let mut thread_helper = self.bits.get_thread_helper();

        // During standard iterations, cumulates the neighbourhood function for the nodes scanned
        // by this thread. During systolic iterations, cumulates the *increase* of the
        // neighbourhood function for the nodes scanned by this thread.
        let mut neighbourhood_function_delta = KahanSummation::new();

        loop {
            // Get work
            let start = std::cmp::min(
                context
                    .cursor
                    .fetch_add(node_granularity, Ordering::Relaxed),
                upper_limit,
            );
            let end = std::cmp::min(start + node_granularity, upper_limit);

            if start == upper_limit {
                break;
            }

            // Do work
            for i in start..end {
                let node = if self.local {
                    self.local_checklist[i]
                } else {
                    i
                };

                // The three cases in which we enumerate successors:
                // 1) A non-systolic computation (we don't know anything, so we enumerate).
                // 2) A systolic, local computation (the node is by definition to be checked, as it comes from the local check list).
                // 3) A systolic, non-local computation in which the node should be checked.
                if !self.systolic || self.local || self.must_be_checked[node] {
                    let mut counter = self.get_current_counter(node);
                    counter.use_thread_helper(&mut thread_helper);
                    for succ in self.graph.successors(node) {
                        if succ != node && self.modified_counter[succ] {
                            if !counter.is_cached() {
                                unsafe {
                                    counter.cache();
                                }
                            }
                            unsafe {
                                counter.merge_unsafe(&self.get_current_counter(succ));
                            }
                        }
                    }

                    let mut post = f64::NAN;
                    let modified_counter = counter.is_changed();

                    // We need the counter value only if the iteration is standard (as we're going to
                    // compute the neighbourhood function cumulating actual values, and not deltas) or
                    // if the counter was actually modified (as we're going to cumulate the neighbourhood
                    // function delta, or at least some centrality).
                    if !self.systolic || modified_counter {
                        post = counter.estimate_count();
                    }
                    if !self.systolic {
                        neighbourhood_function_delta.add(post);
                    }

                    if modified_counter && (self.systolic || do_centrality) {
                        let pre = self.get_current_counter(node).estimate_count();
                        if self.systolic {
                            neighbourhood_function_delta.add(-pre);
                            neighbourhood_function_delta.add(post);
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
                        self.modified_result_counter
                            .set(node, true, Ordering::Relaxed);

                        if self.systolic {
                            debug_assert!(self.rev_graph.is_some());
                            // In systolic computations we must keep track of which counters must
                            // be checked on the next iteration. If we are preparing a local computation,
                            // we do this explicitly, by adding the predecessors of the current
                            // node to a set. Otherwise, we do this implicitly, by setting the
                            // corresponding entry in an array.
                            let rev_graph = self.rev_graph.expect("Should have transpose");
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
                    }

                    // This is slightly subtle: if a counter is not modified, and
                    // the present value was not a modified value in the first place,
                    // then we can avoid updating the result altogether.
                    if modified_counter || self.modified_counter[node] {
                        unsafe {
                            self.get_result_counter(node).set_to(&counter);
                        }
                    }
                } else {
                    // Even if we cannot possibly have changed our value, still our copy
                    // in the result vector might need to be updated because it does not
                    // reflect our current value.
                    if self.modified_counter[node] {
                        unsafe {
                            self.get_result_counter(node)
                                .set_to(&self.get_current_counter(node))
                        };
                    }
                }
            }
        }

        *self.current.lock().unwrap() += neighbourhood_function_delta.value();
    }

    /// Returns the number of HyperLogLog counters that were modified by the last iteration.
    #[inline(always)]
    fn modified_counters(&self) -> usize {
        self.modified_counter.count_ones()
    }

    /// Initialises the approximator.
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn init(&mut self, mut pl: impl ProgressLog) -> Result<()> {
        pl.start("Initializing approximator");
        pl.info(format_args!("Clearing all registers"));
        self.bits.clear();
        self.result_bits.clear();

        pl.info(format_args!("Initializing registers"));
        if let Some(w) = &self.weight {
            pl.info(format_args!("Loading weights"));
            for (i, &node_weight) in w.iter().enumerate() {
                let mut counter = self.bits.get_counter(i);
                for _ in 0..node_weight {
                    counter.add(random());
                }
            }
        } else {
            (0..self.graph.num_nodes()).into_par_iter().for_each(|i| {
                self.get_current_counter(i).add(i);
            });
        }

        self.iteration = 0;
        self.completed = false;
        self.systolic = false;
        self.local = false;
        self.pre_local = false;

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
        if let Some(n) = &mut self.neighbourhood_function {
            pl.info(format_args!("Initializing neighbourhood function"));
            n.clear();
            n.push(self.last);
        }

        pl.info(format_args!("Initializing modified counters"));
        self.modified_counter.fill(true, Ordering::Relaxed);
        pl.done();

        Ok(())
    }
}
