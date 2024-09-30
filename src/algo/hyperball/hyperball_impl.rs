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
    iteration: Option<usize>,
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
        pl: impl ProgressLog,
    ) -> Result<()> {
        let upper_bound = std::cmp::min(upper_bound, self.graph.num_nodes());

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
    fn iterate(&mut self, pl: impl ProgressLog) -> Result<()> {
        todo!()
    }

    /// Returns the number of HyperLogLog counters that were modified by the last iteration.
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

        self.iteration = None;
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
            n.fill(0.0);
        }

        pl.info(format_args!("Initializing modified counters"));
        self.modified_counter.fill(true, Ordering::Relaxed);
        pl.done();

        Ok(())
    }
}
