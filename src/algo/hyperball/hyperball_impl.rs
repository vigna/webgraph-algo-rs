use crate::{prelude::*, utils::*};
use anyhow::{anyhow, Context, Result};
use common_traits::{CastableFrom, IntoAtomic, Number, UpcastableInto};
use dsi_progress_logger::ProgressLog;
use kahan::KahanSum;
use rand::random;
use rayon::{prelude::*, ThreadPool};
use std::{
    hash::{BuildHasher, BuildHasherDefault, DefaultHasher},
    sync::{atomic::*, Mutex},
};
use sux::{
    bits::AtomicBitVec,
    traits::{Succ, Word},
};
use webgraph::traits::RandomAccessGraph;

#[inline(always)]
fn get_register<W: Word>(counter: &[W], register_size: usize, index: usize) -> W {
    let bit_width = register_size;
    let mask = W::MAX >> (W::BITS - bit_width);
    let pos = index * bit_width;
    let word_index = pos / W::BITS;
    let bit_index = pos % W::BITS;

    if bit_index + bit_width <= W::BITS {
        (unsafe { *counter.get_unchecked(word_index) } >> bit_index) & mask
    } else {
        (unsafe { *counter.get_unchecked(word_index) } >> bit_index
            | unsafe { *counter.get_unchecked(word_index + 1) } << (W::BITS - bit_index))
            & mask
    }
}

/// Performs a multiple precision subtraction, leaving the result in the first operand.
/// The operands MUST have the same length.
///
/// # Arguments
/// * `x`: the first operand. This will contain the final result.
/// * `y`: the second operand that will be subtracted from `x`.
#[inline(always)]
pub(super) fn subtract<W: Word>(x: &mut [W], y: &[W]) {
    debug_assert_eq!(x.len(), y.len());
    let mut borrow = false;

    for (x_word, &y) in x.iter_mut().zip(y.iter()) {
        let mut x = *x_word;
        if !borrow {
            borrow = x < y;
        } else if x != W::ZERO {
            x = x.wrapping_sub(W::ONE);
            borrow = x < y;
        } else {
            x = x.wrapping_sub(W::ONE);
        }
        *x_word = x.wrapping_sub(y);
    }
}

#[inline(always)]
pub(super) fn merge_hyperloglog_bitwise<W: Word>(
    x: &mut [W],
    y: &[W],
    msb_mask: &[W],
    lsb_mask: &[W],
    acc: &mut Vec<W>,
    mask: &mut Vec<W>,
    register_size: usize,
) {
    let register_size_minus_1 = register_size - 1;
    let num_words_minus_1 = x.len() - 1;
    let shift_register_size_minus_1 = W::BITS - register_size_minus_1;

    /* We work in two phases. Let H_r (msb_mask) be the mask with the
     * highest bit of each register (of size r) set, and L_r (lsb_mask)
     * be the mask with the lowest bit of each register set.
     * We describe the algorithm on a single word.
     *
     * In the first phase we perform an unsigned strict register-by-register
     * comparison of x and y, using the formula
     *
     * z = ((((y | H_r) - (x & !H_r)) | (y ^ x)) ^ (y | !x)) & H_r
     *
     * Then, we generate a register-by-register mask of all ones or
     * all zeroes, depending on the result of the comparison, using the
     * formula
     *
     * (((z >> r-1 | H_r) - L_r) | H_r) ^ z
     *
     * At that point, it is trivial to select from x and y the right values.
     */

    // We load y | H_r into the accumulator.
    acc.extend(
        y.iter()
            .zip(msb_mask)
            .map(|(&y_word, &msb_word)| y_word | msb_word),
    );

    // We load x & !H_r into mask as temporary storage.
    mask.extend(
        x.iter()
            .zip(msb_mask)
            .map(|(&x_word, &msb_word)| x_word & !msb_word),
    );

    // We subtract x & !H_r, using mask as temporary storage
    subtract(acc, mask);

    // We OR with y ^ x, XOR with (y | !x), and finally AND with H_r.
    acc.iter_mut()
        .zip(x.iter())
        .zip(y.iter())
        .zip(msb_mask.iter())
        .for_each(|(((acc_word, &x_word), &y_word), &msb_word)| {
            *acc_word = ((*acc_word | (y_word ^ x_word)) ^ (y_word | !x_word)) & msb_word
        });

    // We shift by register_size - 1 places and put the result into mask.
    {
        let (mask_last, mask_slice) = mask.split_last_mut().unwrap();
        let (&msb_last, msb_slice) = msb_mask.split_last().unwrap();
        mask_slice
            .iter_mut()
            .zip(acc[0..num_words_minus_1].iter())
            .zip(acc[1..].iter())
            .zip(msb_slice.iter())
            .rev()
            .for_each(|(((mask_word, &acc_word), &next_acc_word), &msb_word)| {
                // W is always unsigned so the shift is always with a 0
                *mask_word = (acc_word >> register_size_minus_1)
                    | (next_acc_word << shift_register_size_minus_1)
                    | msb_word
            });
        *mask_last = (acc[num_words_minus_1] >> register_size_minus_1) | msb_last;
    }

    // We subtract L_r from mask.
    subtract(mask, lsb_mask);

    // We OR with H_r and XOR with the accumulator.
    mask.iter_mut()
        .zip(msb_mask.iter())
        .zip(acc.iter())
        .for_each(|((mask_word, &msb_word), &acc_word)| {
            *mask_word = (*mask_word | msb_word) ^ acc_word
        });

    // Finally, we use mask to select the right bits from x and y and store the result.
    x.iter_mut()
        .zip(y.iter())
        .zip(mask.iter())
        .for_each(|((x_word, &y_word), &mask_word)| {
            *x_word = *x_word ^ ((*x_word ^ y_word) & mask_word);
        });
}

#[inline(always)]
fn count<W: Word + UpcastableInto<u64>>(
    counter: &[W],
    num_registers: usize,
    register_size: usize,
    alpha_m_m: f64,
) -> f64 {
    let mut harmonic_mean = 0.0;
    let mut zeroes = 0;

    for i in 0..num_registers {
        let value = get_register(counter, register_size, i).upcast();
        if value == 0 {
            zeroes += 1;
        }
        harmonic_mean += 1.0 / (1 << value) as f64;
    }

    let mut estimate = alpha_m_m / harmonic_mean;
    if zeroes != 0 && estimate < 2.5 * num_registers as f64 {
        estimate = num_registers as f64 * (num_registers as f64 / zeroes as f64).ln();
    }
    estimate
}

/// Builder for [`HyperBall`].
///
/// Create a builder with [`HyperBallBuilder::new`], edit parameters with
/// its methods, then call [`HyperBallBuilder::build`] on it to create
/// the [`HyperBall`] as a [`Result`].
pub struct HyperBallBuilder<
    'a,
    D: Succ<Input = usize, Output = usize>,
    W: Word + IntoAtomic,
    H: BuildHasher + Clone,
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
    hyper_log_log_settings: HyperLogLogCounterArrayBuilder<H, W>,
}

impl<'a, D: Succ<Input = usize, Output = usize>, G: RandomAccessGraph + Sync>
    HyperBallBuilder<'a, D, usize, BuildHasherDefault<DefaultHasher>, G>
{
    const DEFAULT_GRANULARITY: usize = 16 * 1024;

    /// Creates a new builder with default parameters.
    ///
    /// # Arguments
    /// * `graph`: the direct graph to analyze.
    /// * `cumulative_outdegree`: the degree cumulative function of the graph.
    pub fn new(graph: &'a G, cumulative_outdegree: &'a D) -> Self {
        let hyper_log_log_settings = HyperLogLogCounterArrayBuilder::new_with_word_type()
            .log_2_num_registers(4)
            .num_elements_upper_bound(graph.num_nodes())
            .mem_options(TempMmapOptions::Default);
        Self {
            graph,
            rev_graph: None,
            cumulative_outdegree,
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
        H: BuildHasher + Clone,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
    > HyperBallBuilder<'a, D, W, H, G1, G2>
{
    /// Sets the transposed graph to be used in systolic iterations in [`HyperBall`].
    ///
    /// # Arguments
    /// * `transposed`: the new transposed graph. If [`None`] no transposed graph is used
    ///   and no systolic iterations will be performed by the built [`HyperBall`].
    pub fn transposed<G: RandomAccessGraph + Sync>(
        self,
        transposed: Option<&'a G>,
    ) -> HyperBallBuilder<'a, D, W, H, G1, G> {
        if let Some(t) = transposed {
            assert_eq!(
                t.num_nodes(),
                self.graph.num_nodes(),
                "transposed should have same number of nodes ({}). Got {}.",
                self.graph.num_nodes(),
                t.num_nodes()
            );
            assert_eq!(
                t.num_arcs(),
                self.graph.num_arcs(),
                "transposed should have the same number of arcs ({}). Got {}.",
                self.graph.num_arcs(),
                t.num_arcs()
            );
            debug_assert!(
                check_transposed(self.graph, t),
                "transposed should be the transposed of the direct graph"
            );
        }
        HyperBallBuilder {
            graph: self.graph,
            rev_graph: transposed,
            cumulative_outdegree: self.cumulative_outdegree,
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

    /// Sets the settings for the [`HyperLogLogCounterArray`] used to hold the counters.
    ///
    /// # Arguments
    /// * `settings`: the new settings to use.
    pub fn hyperloglog_settings<W2: Word + IntoAtomic, H2: BuildHasher + Clone>(
        self,
        settings: HyperLogLogCounterArrayBuilder<H2, W2>,
    ) -> HyperBallBuilder<'a, D, W2, H2, G1, G2> {
        HyperBallBuilder {
            graph: self.graph,
            rev_graph: self.rev_graph,
            cumulative_outdegree: self.cumulative_outdegree,
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
        W: Word + IntoAtomic + UpcastableInto<u64> + CastableFrom<u64>,
        H: BuildHasher + Clone,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
    > HyperBallBuilder<'a, D, W, H, G1, G2>
{
    /// Builds the [`HyperBall`] instance with the specified settings and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// * `pl`: A progress logger.
    #[allow(clippy::type_complexity)]
    pub fn build(
        self,
        pl: &mut impl ProgressLog,
    ) -> Result<HyperBall<'a, G1, G2, D, W, HyperLogLogCounterArray<G1::Label, W, H>>> {
        let num_nodes = self.graph.num_nodes();

        pl.info(format_args!("Initializing HyperLogLogCounterArrays"));
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
            words_per_counter: bits.words_per_counter(),
            lsb_mask: bits.lsb_mask.as_slice().into(),
            msb_mask: bits.msb_mask.as_slice().into(),
            register_size: bits.register_size(),
            alpha_m_m: bits.alpha_m_m,
            num_registers: bits.num_registers(),
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
            neighbourhood_function: Vec::new(),
            last: 0.0,
            current: Mutex::new(0.0),
            modified_counter,
            modified_result_counter,
            local_checklist: Vec::new(),
            local_next_must_be_checked: Mutex::new(Vec::new()),
            must_be_checked,
            next_must_be_checked,
            relative_increment: 0.0,
            granularity,
            iteration_context: IterationContext::default(),
            _phantom_data: std::marker::PhantomData,
        })
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
    W: Word + IntoAtomic,
    A: CounterArray<G1::Label, W>,
> {
    /// The direct graph to analyze
    graph: &'a G1,
    /// The transposed of the graph to analyze
    rev_graph: Option<&'a G2>,
    /// The cumulative list of outdegrees
    cumulative_outdegree: &'a D,
    /// A slice of nonegative node weights
    weight: Option<&'a [usize]>,
    /// The base number of nodes per task. Must be a multiple of `bits.chuk_size()`
    granularity: usize,
    /// The current status of Hyperball
    bits: A,
    /// The new status of Hyperball after an iteration
    result_bits: A,
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
    /// The neighbourhood fuction
    neighbourhood_function: Vec<f64>,
    /// The value computed by the last iteration
    last: f64,
    /// The value computed by the current iteration
    current: Mutex<f64>,
    /// `modified_counter[i]` is `true` if `bits.get_counter(i)` has been modified
    modified_counter: AtomicBitVec,
    /// `modified_result_counter[i]` is `true` if `result_bits.get_counter(i)` has been modified
    modified_result_counter: AtomicBitVec,
    /// If [`Self::local`] is `true`, the sorted list of nodes that should be scanned
    local_checklist: Vec<G1::Label>,
    /// If [`Self::pre_local`] is `true`, the set of nodes that should be scanned on the next iteration
    local_next_must_be_checked: Mutex<Vec<G1::Label>>,
    /// Used in systolic iterations to keep track of nodes to check
    must_be_checked: AtomicBitVec,
    /// Used in systolic iterations to keep track of nodes to check in the next iteration
    next_must_be_checked: AtomicBitVec,
    /// The relative increment of the neighbourhood function for the last iteration
    relative_increment: f64,
    /// Context used in a single iteration
    iteration_context: IterationContext,
    words_per_counter: usize,
    msb_mask: Box<[W]>,
    lsb_mask: Box<[W]>,
    register_size: usize,
    num_registers: usize,
    alpha_m_m: f64,
    _phantom_data: std::marker::PhantomData<W>,
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        D: Succ<Input = usize, Output = usize> + Sync,
        W: Word + CastableFrom<u64> + UpcastableInto<u64> + IntoAtomic,
        A: CounterArray<G1::Label, W> + Sync + Send,
    > HyperBall<'a, G1, G2, D, W, A>
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

    /// Returns the neighbourhood function computed by this instance.
    pub fn neighbourhood_function(&self) -> Result<Vec<f64>> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else {
            Ok(self.neighbourhood_function.clone())
        }
    }

    /// Returns the sum of distances computed by this instance if requested.
    pub fn sum_of_distances(&self) -> Result<Vec<f64>> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else if let Some(distances) = &self.sum_of_distances {
            Ok(distances.lock().unwrap().to_vec())
        } else {
            Err(anyhow!("Sum of distances were not requested. Use builder.with_sum_of_distances(true) while building HyperBall to compute them"))
        }
    }

    /// Returns the harmonic centralities (sum of inverse distances) computed by this instance if requested.
    pub fn harmonic_centralities(&self) -> Result<Vec<f64>> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else if let Some(distances) = &self.sum_of_inverse_distances {
            Ok(distances.lock().unwrap().to_vec())
        } else {
            Err(anyhow!("Sum of inverse distances were not requested. Use builder.with_sum_of_inverse_distances(true) while building HyperBall to compute them"))
        }
    }

    /// Returns the discounted centralities of the specified index computed by this instance.
    ///
    /// # Arguments
    /// * `index`: the index of the requested discounted centrality.
    pub fn discounted_centrality(&self, index: usize) -> Result<Vec<f64>> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else {
            let d = self.discounted_centralities.get(index);
            if let Some(distaces) = d {
                Ok(distaces.lock().unwrap().to_vec())
            } else {
                Err(anyhow!(
                    "Discount centrality of index {} does not exist",
                    index
                ))
            }
        }
    }

    /// Computes and returns the closeness centralities from the sum of distances computed by this instance.
    pub fn closeness_cetrality(&self) -> Result<Vec<f64>> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else if let Some(distances) = &self.sum_of_distances {
            Ok(distances
                .lock()
                .unwrap()
                .iter()
                .map(|&d| if d == 0.0 { 0.0 } else { d.recip() })
                .collect())
        } else {
            Err(anyhow!("Sum of distances were not requested. Use builder.with_sum_of_distances(true) while building HyperBall to compute closeness centrality"))
        }
    }

    /// Computes and returns the lin centralities from the sum of distances computed by this instance.
    ///
    /// Note that lin's index for isolated nodes is by (our) definition one (it's smaller than any other node).
    pub fn lin_centrality(&self) -> Result<Vec<f64>> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else if let Some(distances) = &self.sum_of_distances {
            Ok(distances
                .lock()
                .unwrap()
                .iter()
                .enumerate()
                .map(|(i, &d)| {
                    if d == 0.0 {
                        1.0
                    } else {
                        let count = unsafe { self.bits.get_counter_from_shared(i) }.count();
                        count * count / d
                    }
                })
                .collect())
        } else {
            Err(anyhow!("Sum of distances were not requested. Use builder.with_sum_of_distances(true) while building HyperBall to compute lin centrality"))
        }
    }

    /// Computes and returns the nieminen centralities from the sum of distances computed by this instance.
    pub fn nieminen_centrality(&self) -> Result<Vec<f64>> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else if let Some(distances) = &self.sum_of_distances {
            Ok(distances
                .lock()
                .unwrap()
                .iter()
                .enumerate()
                .map(|(i, &d)| {
                    let count = unsafe { self.bits.get_counter_from_shared(i) }.count();
                    (count * count) - d
                })
                .collect())
        } else {
            Err(anyhow!("Sum of distances were not requested. Use builder.with_sum_of_distances(true) while building HyperBall to compute lin centrality"))
        }
    }

    /// Reads from the internal [`HyperLogLogCounterArray`] and estimates the number of nodes reachable
    /// from the specified node.
    ///
    /// # Arguments
    /// * `node`: the index of the node to compute reachable nodes from.
    pub fn reachable_nodes_from(&self, node: usize) -> Result<f64> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else {
            Ok(unsafe { self.bits.get_counter_from_shared(node) }.count())
        }
    }

    /// Reads from the internal [`HyperLogLogCounterArray`] and estimates the number of nodes reachable
    /// from every node of the graph.
    ///
    /// `hyperball.reachable_nodes().unwrap()[i]` is equal to `hyperball.reachable_nodes_from(i).unwrap()`.
    pub fn reachable_nodes(&self) -> Result<Vec<f64>> {
        if self.iteration == 0 {
            Err(anyhow!(
                "HyperBall was not run. Please call self.run(...) before accessing computed fields"
            ))
        } else {
            Ok((0..self.graph.num_nodes())
                .map(|n| unsafe { self.bits.get_counter_from_shared(n) }.count())
                .collect())
        }
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        D: Succ<Input = usize, Output = usize> + Sync,
        W: Word + IntoAtomic + UpcastableInto<u64> + CastableFrom<u64>,
        A: CounterArray<G1::Label, W>,
    > HyperBall<'a, G1, G2, D, W, A>
{
    /// Swaps the undelying backend [`HyperLogLogCounterArray`] between current and result.
    #[inline(always)]
    fn swap_arrays(&mut self) {
        self.bits.swap_with(&mut self.result_bits);
        std::mem::swap(
            &mut self.modified_counter,
            &mut self.modified_result_counter,
        );
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        D: Succ<Input = usize, Output = usize> + Sync,
        W: Word + CastableFrom<u64> + UpcastableInto<u64> + IntoAtomic,
        A: CounterArray<G1::Label, W> + Sync + Send,
    > HyperBall<'a, G1, G2, D, W, A>
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
            thread_pool.install(|| self.modified_result_counter.fill(false, Ordering::Relaxed));
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
                granularity = (granularity + W::BITS - 1) & W::BITS.wrapping_neg();
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
        let mut acc = Vec::with_capacity(self.words_per_counter);
        let mut mask = Vec::with_capacity(self.words_per_counter);

        // During standard iterations, cumulates the neighbourhood function for the nodes scanned
        // by this thread. During systolic iterations, cumulates the *increase* of the
        // neighbourhood function for the nodes scanned by this thread.
        let mut neighbourhood_function_delta = KahanSum::new_with_value(0.0);

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

                // The three cases in which we enumerate successors:
                // 1) A non-systolic computation (we don't know anything, so we enumerate).
                // 2) A systolic, local computation (the node is by definition to be checked, as it comes from the local check list).
                // 3) A systolic, non-local computation in which the node should be checked.
                if !self.systolic || self.local || self.must_be_checked[node] {
                    // We write directly to the result
                    let counter = unsafe {
                        // Safety: no other thread will ever read from or write to this counter
                        self.result_bits.get_mut_slice(node)
                    };
                    let old_counter = self.bits.get_slice(node);
                    let mut modified = false;
                    for succ in self.graph.successors(node) {
                        if succ != node && self.modified_counter[succ] {
                            visited_arcs += 1;
                            if !modified {
                                counter.copy_from_slice(old_counter);
                                modified = true;
                            }
                            acc.clear();
                            mask.clear();
                            merge_hyperloglog_bitwise(
                                counter,
                                self.bits.get_slice(succ),
                                &self.msb_mask,
                                &self.lsb_mask,
                                &mut acc,
                                &mut mask,
                                self.register_size,
                            );
                        }
                    }

                    let mut post = f64::NAN;
                    let modified_counter = if modified {
                        counter != old_counter
                    } else {
                        false
                    };

                    // We need the counter value only if the iteration is standard (as we're going to
                    // compute the neighbourhood function cumulating actual values, and not deltas) or
                    // if the counter was actually modified (as we're going to cumulate the neighbourhood
                    // function delta, or at least some centrality).
                    if !self.systolic || modified_counter {
                        post = count(
                            counter,
                            self.num_registers,
                            self.register_size,
                            self.alpha_m_m,
                        );
                    }
                    if !self.systolic {
                        neighbourhood_function_delta += post;
                    }

                    if modified_counter && (self.systolic || do_centrality) {
                        let pre = count(
                            old_counter,
                            self.num_registers,
                            self.register_size,
                            self.alpha_m_m,
                        );
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

                        modified_counters += 1;
                    }

                    // This is slightly subtle: if a counter is not modified, and
                    // the present value was not a modified value in the first place,
                    // then we can avoid updating the result altogether.
                    if !modified && self.modified_counter[node] {
                        counter.copy_from_slice(old_counter);
                    }
                } else {
                    // Even if we cannot possibly have changed our value, still our copy
                    // in the result vector might need to be updated because it does not
                    // reflect our current value.
                    if self.modified_counter[node] {
                        unsafe {
                            // Safety: we are only ever writing to the result array and
                            // no counter is ever written to more than once
                            self.result_bits
                                .get_mut_slice(node)
                                .copy_from_slice(self.bits.get_slice(node))
                        };
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
        thread_pool.join(|| self.bits.clear(), || self.result_bits.clear());

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
            thread_pool.install(|| {
                (0..self.graph.num_nodes()).into_par_iter().for_each(|i| {
                    unsafe { self.bits.get_counter_from_shared(i) }.add(i);
                });
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
        thread_pool.install(|| self.modified_counter.fill(true, Ordering::Relaxed));

        pl.done();

        Ok(())
    }
}
