use crate::{
    prelude::*,
    utils::{HyperLogLogCounter, HyperLogLogCounterArray, HyperLogLogCounterArrayBuilder},
};
use anyhow::{Context, Result};
use common_traits::*;
use dsi_progress_logger::ProgressLog;
use rand::random;
use rayon::prelude::*;
use std::{
    hash::{BuildHasher, BuildHasherDefault, DefaultHasher},
    sync::atomic::Ordering,
};
use sux::{bits::*, traits::*};
use webgraph::traits::RandomAccessGraph;

pub struct HyperBall<
    'a,
    G1: RandomAccessGraph,
    G2: RandomAccessGraph,
    W: Word + IntoAtomic = usize,
    H: BuildHasher = BuildHasherDefault<DefaultHasher>,
> {
    /// The direct graph to analyze
    graph: &'a G1,
    /// The transposed of the graph to analyze
    rev_graph: Option<&'a G2>,
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
    sum_of_distances: Option<Vec<f64>>,
    /// The sum of inverse distances from each given node, if requested
    sum_of_inverse_distances: Option<Vec<f64>>,
    /// A number of discounted centralities to be computed, possibly none
    discount_functions: Vec<Box<dyn Fn(usize) -> f64 + Sync>>,
    /// The overall discount centrality for every [`Self::discount_functions`]
    discounted_centralities: Vec<Vec<f64>>,
    /// The neighbourhood fuction if requested
    neighbourhood_function: Option<Vec<f64>>,
    /// The value computed by the last iteration
    last: f64,
    /// The value computed by the current iteration
    current: f64,
    /// `modified_counter[i]` is `true` if `bits.get_counter(i)` has been modified
    modified_counter: AtomicBitVec,
    /// `modified_result_counter[i]` is `true` if `result_bits.get_counter(i)` has been modified
    modified_result_counter: AtomicBitVec,
    /// If [`Self::local`] is `true`, the sorted list of nodes that should be scanned
    local_checklist: Vec<usize>,
    /// If [`Self::pre_local`] is `true`, the set of nodes that should be scanned on the next iteration
    local_next_must_be_checked: Vec<usize>,
    /// Used in systolic iterations to keep track of nodes to check
    must_be_checked: AtomicBitVec,
    /// Used in systolic iterations to keep track of nodes to check in the next iteration
    next_must_be_checked: AtomicBitVec,
    /// The relative increment of the neighbourhood function for the last iteration
    relative_increment: f64,
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        W: Word + TryFrom<u64> + UpcastableInto<u64> + IntoAtomic,
        H: BuildHasher + Sync,
    > HyperBall<'a, G1, G2, W, H>
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

        pl.start(format!(
            "Running Hyperball for a maximum of {} iterations and a threshold of {:?}",
            upper_bound, threshold
        ));

        self.init(pl.clone())
            .with_context(|| "Could not initialize approximator")?;

        for i in 0..upper_bound {
            pl.info(format_args!("Executing iteration {}", i));

            self.iterate(pl.clone())
                .with_context(|| format!("Could not perform iteration {}", i))?;

            if self.modified_counters() == 0 {
                pl.info(format_args!(
                    "Terminating appoximation after {} iteration(s) by stabilisation",
                    i
                ));
                break;
            }

            if let Some(t) = threshold {
                todo!("relative increment check");
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

impl<'a, G1: RandomAccessGraph, G2: RandomAccessGraph, W: Word + IntoAtomic, H: BuildHasher>
    HyperBall<'a, G1, G2, W, H>
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
        W: Word + TryFrom<u64> + UpcastableInto<u64> + IntoAtomic,
        H: BuildHasher + Sync,
    > HyperBall<'a, G1, G2, W, H>
where
    W::AtomicType: AtomicUnsignedInt + AsBytes,
{
    /// Performs a new iteration of HyperBall.
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn iterate(&mut self, mut pl: impl ProgressLog) -> Result<()> {
        pl.start(format!("Performing iteration {}", self.iteration));

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
        self.current = if self.systolic { self.last } else { 0.0 };

        // If we completed the last iteration in pre-local mode, we MUST run in local mode.
        self.local = self.pre_local;

        // We run in pre-local mode if we are systolic and few nodes where modified.
        self.pre_local =
            self.systolic && modified_counters < (num_nodes * num_nodes) / (num_arcs * 10);

        if self.systolic {
            pl.info(format_args!(
                "Startig systolic iteration (local: {}, pre_local: {})",
                self.local, self.pre_local
            ));
        } else {
            pl.info(format_args!("Starting standard iteration"));
        }

        pl.info(format_args!("Preparing modified_result_counter"));
        if previous_was_local {
            for node in self.local_checklist.iter() {
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
            self.local_next_must_be_checked.par_sort_unstable();
            self.local_next_must_be_checked.dedup();
            self.local_checklist.clear();
            std::mem::swap(
                &mut self.local_checklist,
                &mut self.local_next_must_be_checked,
            );
        } else if self.systolic {
            pl.info(format_args!("Preparing systolic flags"));
            // Systolic, non-local computations store the could-be-modified set implicitly into Self::next_must_be_checked.
            self.next_must_be_checked.fill(false, Ordering::Relaxed);

            // If the previous computation wasn't systolic, we must assume that all registers could have changed.
            if !previous_was_systolic {
                self.must_be_checked.fill(true, Ordering::Relaxed);
            }
        }

        rayon::broadcast(|c| self.parallel_task(c));

        self.swap_backend();
        if self.systolic {
            std::mem::swap(&mut self.must_be_checked, &mut self.next_must_be_checked);
        }

        self.last = self.current;
        // We enforce monotonicity. Non-monotonicity can only be caused
        // by approximation errors.
        if let Some(n_function) = &mut self.neighbourhood_function {
            let &last_output = n_function
                .as_slice()
                .last()
                .expect("Should always have at least 1 element");
            if self.current < last_output {
                self.current = last_output;
            }
            self.relative_increment = self.current / last_output;

            pl.info(format_args!(
                "Pairs: {} ({}%)",
                self.current,
                (self.current * 100.0) / (num_nodes * num_nodes) as f64
            ));
            pl.info(format_args!(
                "Absolute increment: {}",
                self.current - last_output
            ));
            pl.info(format_args!(
                "Relative increment: {}",
                self.relative_increment
            ));

            n_function.push(self.current);
        }

        self.iteration += 1;

        pl.done();

        Ok(())
    }

    /// The parallel operations to be performed each iteration.
    ///
    /// # Arguments:
    /// - `broadcast_context`: the context of the rayon::broadcast function
    fn parallel_task(&self, broadcast_context: rayon::BroadcastContext) {
        todo!()
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
            for (i, node_weight) in w.iter().enumerate() {
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
        if let Some(distances) = &mut self.sum_of_distances {
            distances.fill(f64::ZERO);
        }
        if let Some(distances) = &mut self.sum_of_inverse_distances {
            distances.fill(f64::ZERO);
        }
        pl.info(format_args!("Initializing centralities"));
        for centralities in self.discounted_centralities.iter_mut() {
            centralities.fill(0.0);
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
