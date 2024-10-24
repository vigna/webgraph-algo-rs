use crate::{
    algo::{
        bfv::ParallelBreadthFirstVisitFastCB,
        diameter::{scc_graph::SccGraph, SumSweepOutputLevel},
        strongly_connected_components::TarjanStronglyConnectedComponents,
    },
    prelude::*,
    utils::*,
};
use anyhow::{ensure, Context, Result};
use dsi_progress_logger::*;
use nonmax::NonMaxUsize;
use rayon::prelude::*;
use std::{
    borrow::Borrow,
    sync::{
        atomic::{AtomicUsize, Ordering},
        RwLock,
    },
};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

/// Builder for [`SumSweepDirectedDiameterRadius`].
pub struct SumSweepDirectedDiameterRadiusBuilder<
    'a,
    G1: RandomAccessGraph + Sync,
    G2: RandomAccessGraph + Sync,
    T,
    C: StronglyConnectedComponents<G1> = TarjanStronglyConnectedComponents<G1>,
> {
    graph: &'a G1,
    rev_graph: &'a G2,
    output: SumSweepOutputLevel,
    radial_vertices: Option<AtomicBitVec>,
    threads: T,
    mem_options: TempMmapOptions,
    _marker: std::marker::PhantomData<C>,
}

impl<'a, G1: RandomAccessGraph + Sync, G2: RandomAccessGraph + Sync>
    SumSweepDirectedDiameterRadiusBuilder<
        'a,
        G1,
        G2,
        Threads,
        TarjanStronglyConnectedComponents<G1>,
    >
{
    /// Creates a new builder with default parameters.
    ///
    /// # Arguments
    /// * `graph`: the direct graph to analyze.
    /// * `transposed_graph`: the transposed of `graph`.
    /// * `output`: the output to generate.
    pub fn new(graph: &'a G1, transposed_graph: &'a G2, output: SumSweepOutputLevel) -> Self {
        assert_eq!(
            transposed_graph.num_nodes(),
            graph.num_nodes(),
            "transposed should have same number of nodes ({}). Got {}.",
            graph.num_nodes(),
            transposed_graph.num_nodes()
        );
        assert_eq!(
            transposed_graph.num_arcs(),
            graph.num_arcs(),
            "transposed should have the same number of arcs ({}). Got {}.",
            graph.num_arcs(),
            transposed_graph.num_arcs()
        );
        debug_assert!(
            check_transposed(graph, transposed_graph),
            "transposed should be the transposed of the direct graph"
        );
        Self {
            graph,
            rev_graph: transposed_graph,
            output,
            radial_vertices: None,
            threads: Threads::Default,
            mem_options: TempMmapOptions::Default,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        T,
        C: StronglyConnectedComponents<G1>,
    > SumSweepDirectedDiameterRadiusBuilder<'a, G1, G2, T, C>
{
    /// Sets the radial vertices with a bit vector.
    ///
    /// # Arguments
    /// * `radial_vertices`: the [`AtomicBitVec`] where `v[i]` is `true` if it is a radial
    ///   vertex. If [`None`], the set is automatically chosen as the set of vertices that
    ///   are in the biggest strongly connected component, or that are able to reach the biggest
    ///   strongly connected component.
    pub fn radial_vertices(mut self, radial_vertices: Option<AtomicBitVec>) -> Self {
        if let Some(v) = radial_vertices.as_ref() {
            assert_eq!(v.len(), self.graph.num_nodes());
        }
        self.radial_vertices = radial_vertices;
        self
    }

    /// Sets the memory options used by the support arrays of the
    /// [`SumSweepDirectedDiameterRadius`] instance.
    ///
    /// # Argumets
    /// * `settings`: the new settings to use.
    pub fn mem_settings(mut self, settings: TempMmapOptions) -> Self {
        self.mem_options = settings;
        self
    }

    /// Sets the [`SumSweepDirectedDiameterRadius`] instance to use the default [`rayon::ThreadPool`].
    pub fn default_threadpool(
        self,
    ) -> SumSweepDirectedDiameterRadiusBuilder<'a, G1, G2, Threads, C> {
        SumSweepDirectedDiameterRadiusBuilder {
            graph: self.graph,
            rev_graph: self.rev_graph,
            output: self.output,
            radial_vertices: self.radial_vertices,
            threads: Threads::Default,
            mem_options: self.mem_options,
            _marker: self._marker,
        }
    }

    /// Sets the [`SumSweepDirectedDiameterRadius`] instance to use a custom [`rayon::ThreadPool`] with the
    /// specified number of threads.
    ///
    /// # Arguments
    /// * `num_threads`: the number of threads to use for the new `ThreadPool`.
    pub fn num_threads(
        self,
        num_threads: usize,
    ) -> SumSweepDirectedDiameterRadiusBuilder<'a, G1, G2, Threads, C> {
        SumSweepDirectedDiameterRadiusBuilder {
            graph: self.graph,
            rev_graph: self.rev_graph,
            output: self.output,
            radial_vertices: self.radial_vertices,
            threads: Threads::NumThreads(num_threads),
            mem_options: self.mem_options,
            _marker: self._marker,
        }
    }

    /// Sets the [`SumSweepDirectedDiameterRadius`] instance to use the provided [`rayon::ThreadPool`].
    ///
    /// # Arguments
    /// * `threadpool`: the custom `ThreadPool` to use.
    pub fn threadpool<T2: Borrow<rayon::ThreadPool> + Clone + Sync>(
        self,
        threads: T2,
    ) -> SumSweepDirectedDiameterRadiusBuilder<'a, G1, G2, T2, C> {
        SumSweepDirectedDiameterRadiusBuilder {
            graph: self.graph,
            rev_graph: self.rev_graph,
            output: self.output,
            radial_vertices: self.radial_vertices,
            threads,
            mem_options: self.mem_options,
            _marker: self._marker,
        }
    }

    /// Sets the algorithm to use to compute the strongly connected components for the graph.
    pub fn scc<C2: StronglyConnectedComponents<G1>>(
        self,
    ) -> SumSweepDirectedDiameterRadiusBuilder<'a, G1, G2, T, C2> {
        SumSweepDirectedDiameterRadiusBuilder {
            graph: self.graph,
            rev_graph: self.rev_graph,
            output: self.output,
            radial_vertices: self.radial_vertices,
            threads: self.threads,
            mem_options: self.mem_options,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        C: StronglyConnectedComponents<G1> + Sync,
    > SumSweepDirectedDiameterRadiusBuilder<'a, G1, G2, Threads, C>
{
    /// Builds the [`SumSweepDirectedDiameterRadius`] instance with the specified settings and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the build process. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    #[allow(clippy::type_complexity)]
    pub fn build(
        self,
        pl: impl ProgressLog,
    ) -> Result<
        SumSweepDirectedDiameterRadius<
            'a,
            G1,
            G2,
            C,
            ParallelBreadthFirstVisitFastCB<'a, G1, rayon::ThreadPool>,
            ParallelBreadthFirstVisitFastCB<'a, G2, rayon::ThreadPool>,
            rayon::ThreadPool,
        >,
    > {
        let direct_visit = ParallelBreadthFirstVisitFastCB::with_threads(
            self.graph,
            VISIT_GRANULARITY,
            self.threads.build(),
        );
        let transposed_visit = ParallelBreadthFirstVisitFastCB::with_threads(
            self.rev_graph,
            VISIT_GRANULARITY,
            self.threads.build(),
        );
        SumSweepDirectedDiameterRadius::new(
            self.graph,
            self.rev_graph,
            self.output,
            direct_visit,
            transposed_visit,
            self.threads.build(),
            self.radial_vertices,
            self.mem_options,
            pl,
        )
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        T: Borrow<rayon::ThreadPool> + Clone + Sync,
        C: StronglyConnectedComponents<G1> + Sync,
    > SumSweepDirectedDiameterRadiusBuilder<'a, G1, G2, T, C>
{
    /// Builds the [`SumSweepDirectedDiameterRadius`] instance with the specified settings and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the build process. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    #[allow(clippy::type_complexity)]
    pub fn build(
        self,
        pl: impl ProgressLog,
    ) -> Result<
        SumSweepDirectedDiameterRadius<
            'a,
            G1,
            G2,
            C,
            ParallelBreadthFirstVisitFastCB<'a, G1, T>,
            ParallelBreadthFirstVisitFastCB<'a, G2, T>,
            T,
        >,
    > {
        let direct_visit = ParallelBreadthFirstVisitFastCB::with_threads(
            self.graph,
            VISIT_GRANULARITY,
            self.threads.clone(),
        );
        let transposed_visit = ParallelBreadthFirstVisitFastCB::with_threads(
            self.rev_graph,
            VISIT_GRANULARITY,
            self.threads.clone(),
        );
        SumSweepDirectedDiameterRadius::new(
            self.graph,
            self.rev_graph,
            self.output,
            direct_visit,
            transposed_visit,
            self.threads,
            self.radial_vertices,
            self.mem_options,
            pl,
        )
    }
}

const VISIT_GRANULARITY: usize = 32;

pub struct SumSweepDirectedDiameterRadius<
    'a,
    G1: RandomAccessGraph + Sync,
    G2: RandomAccessGraph + Sync,
    C: StronglyConnectedComponents<G1>,
    V1: BreadthFirstGraphVisit,
    V2: BreadthFirstGraphVisit,
    T: Borrow<rayon::ThreadPool>,
> {
    graph: &'a G1,
    reversed_graph: &'a G2,
    number_of_nodes: usize,
    output: SumSweepOutputLevel,
    radial_vertices: AtomicBitVec<MmapSlice<AtomicUsize>>,
    diameter_lower_bound: usize,
    radius_upper_bound: usize,
    /// A vertex whose eccentricity equals the diameter.
    diameter_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    radius_vertex: usize,
    /// Number of iterations performed until now.
    iterations: usize,
    lower_bound_forward_eccentricities: MmapSlice<usize>,
    upper_bound_forward_eccentricities: MmapSlice<usize>,
    lower_bound_backward_eccentricities: MmapSlice<usize>,
    upper_bound_backward_eccentricities: MmapSlice<usize>,
    /// Number of iterations before the radius is found.
    radius_iterations: Option<NonMaxUsize>,
    /// Number of iterations before the diameter is found.
    diameter_iterations: Option<NonMaxUsize>,
    /// Number of iterations before all forward eccentricities are found.
    forward_eccentricities_iterations: Option<NonMaxUsize>,
    /// Number of iterations before all eccentricities are found.
    all_eccentricities_iterations: Option<NonMaxUsize>,
    strongly_connected_components: C,
    /// The strongly connected components diagram.
    strongly_connected_components_graph: SccGraph<G1, G2, C>,
    /// Total forward distance from already processed vertices (used as tie-break for the choice
    /// of the next vertex to process).
    total_forward_distance: MmapSlice<usize>,
    /// Total backward distance from already processed vertices (used as tie-break for the choice
    /// of the next vertex to process).
    total_backward_distance: MmapSlice<usize>,
    compute_radial_vertices: bool,
    visit: V1,
    transposed_visit: V2,
    threadpool: T,
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        C: StronglyConnectedComponents<G1> + Sync,
        V1: BreadthFirstGraphVisit + Sync,
        V2: BreadthFirstGraphVisit + Sync,
        T: Borrow<rayon::ThreadPool> + Sync,
    > SumSweepDirectedDiameterRadius<'a, G1, G2, C, V1, V2, T>
{
    #[allow(clippy::too_many_arguments)]
    fn new(
        graph: &'a G1,
        reversed_graph: &'a G2,
        output: SumSweepOutputLevel,
        direct_visit: V1,
        transposed_visit: V2,
        threadpool: T,
        radial_vertices: Option<AtomicBitVec>,
        options: TempMmapOptions,
        pl: impl ProgressLog,
    ) -> Result<Self> {
        let nn = graph.num_nodes();
        ensure!(
            nn < usize::MAX,
            "Graph should have a number of nodes < usize::MAX"
        );

        let scc = C::compute(graph, false, options.clone(), pl.clone())
            .with_context(|| "Cannot compute strongly connected components")?;

        let compute_radial_vertices = radial_vertices.is_none();
        let acc_radial = if let Some(r) = radial_vertices {
            debug_assert_eq!(r.len(), nn);
            r
        } else {
            AtomicBitVec::new(nn)
        };
        let (v, len) = acc_radial.into_raw_parts();
        let mmap = MmapSlice::from_vec(v, options.clone())
            .with_context(|| "Cannot create radial vertices bitvec slice")?;
        let acc_radial = unsafe { AtomicBitVec::from_raw_parts(mmap, len) };

        let scc_graph = SccGraph::new(graph, reversed_graph, &scc, options.clone(), pl.clone())
            .with_context(|| "Cannot create strongly connected components graph")?;

        debug_assert_eq!(graph.num_nodes(), reversed_graph.num_nodes());
        debug_assert_eq!(graph.num_arcs(), reversed_graph.num_arcs());
        debug_assert!(
            check_transposed(graph, reversed_graph),
            "reversed_graph should be the transposed of graph"
        );

        pl.info(format_args!("Initializing data structure"));

        let lower_forward = MmapSlice::from_vec(vec![0; nn], options.clone())
            .with_context(|| "Cannot create lower bound forward eccentricities slice")?;
        let lower_backward = MmapSlice::from_vec(vec![0; nn], options.clone())
            .with_context(|| "Cannot create lower bound backwards eccentricities slice")?;
        let upper_forward = MmapSlice::from_vec(vec![nn + 1; nn], options.clone())
            .with_context(|| "Cannot create upper bound forward eccentricities slice")?;
        let upper_backward = MmapSlice::from_vec(vec![nn + 1; nn], options.clone())
            .with_context(|| "Cannot create upper bound backwards eccentricities slice")?;
        let total_forward = MmapSlice::from_vec(vec![0; nn], options.clone())
            .with_context(|| "Cannot create total forward distances slice")?;
        let total_backward = MmapSlice::from_vec(vec![0; nn], options.clone())
            .with_context(|| "Cannot create total backards distances slice")?;

        Ok(SumSweepDirectedDiameterRadius {
            graph,
            reversed_graph,
            number_of_nodes: nn,
            total_forward_distance: total_forward,
            total_backward_distance: total_backward,
            lower_bound_forward_eccentricities: lower_forward,
            upper_bound_forward_eccentricities: upper_forward,
            lower_bound_backward_eccentricities: lower_backward,
            upper_bound_backward_eccentricities: upper_backward,
            strongly_connected_components_graph: scc_graph,
            strongly_connected_components: scc,
            diameter_lower_bound: 0,
            radius_upper_bound: usize::MAX,
            output,
            radius_iterations: None,
            diameter_iterations: None,
            all_eccentricities_iterations: None,
            forward_eccentricities_iterations: None,
            iterations: 0,
            radial_vertices: acc_radial,
            radius_vertex: 0,
            diameter_vertex: 0,
            compute_radial_vertices,
            visit: direct_visit,
            transposed_visit,
            threadpool,
        })
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        C: StronglyConnectedComponents<G1> + Sync,
        V1: BreadthFirstGraphVisit + Sync,
        V2: BreadthFirstGraphVisit + Sync,
        T: Borrow<rayon::ThreadPool> + Sync,
    > SumSweepDirectedDiameterRadius<'a, G1, G2, C, V1, V2, T>
{
    fn incomplete_forward_vertex(&self, index: usize) -> bool {
        self.lower_bound_forward_eccentricities[index]
            != self.upper_bound_forward_eccentricities[index]
    }

    fn incomplete_backward_vertex(&self, index: usize) -> bool {
        self.lower_bound_backward_eccentricities[index]
            != self.upper_bound_backward_eccentricities[index]
    }

    fn forward_eccentricity(&self, index: usize) -> Option<usize> {
        if self.incomplete_forward_vertex(index) {
            None
        } else {
            debug_assert_eq!(
                self.lower_bound_forward_eccentricities[index],
                self.upper_bound_forward_eccentricities[index]
            );
            Some(self.lower_bound_forward_eccentricities[index])
        }
    }

    fn backward_eccentricity(&self, index: usize) -> Option<usize> {
        if self.incomplete_backward_vertex(index) {
            None
        } else {
            debug_assert_eq!(
                self.lower_bound_backward_eccentricities[index],
                self.upper_bound_backward_eccentricities[index]
            );
            Some(self.lower_bound_backward_eccentricities[index])
        }
    }

    /// Performs `iterations` steps of the SumSweep heuristic, starting from vertex `start`.
    ///
    /// # Arguments
    /// * `start`: The starting vertex.
    /// * `iterations`: The number of iterations.
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn sum_sweep_heuristic(
        &mut self,
        start: usize,
        iterations: usize,
        pl: impl ProgressLog,
    ) -> Result<()> {
        pl.info(format_args!(
            "Performing initial SumSweep visit from {}.",
            start
        ));
        self.step_sum_sweep(Some(start), true, pl.clone())
            .with_context(|| "Could not perform initial SumSweep visit")?;

        for i in 2..=iterations {
            if i % 2 == 0 {
                let v = math::filtered_argmax(
                    &self.total_backward_distance,
                    &self.lower_bound_backward_eccentricities,
                    |i, _| self.incomplete_backward_vertex(i),
                );
                pl.info(format_args!(
                    "Performing backwards SumSweep visit from {:?}",
                    v
                ));
                self.step_sum_sweep(v, false, pl.clone())
                    .with_context(|| format!("Could not perform backwards visit from {:?}", v))?;
            } else {
                let v = math::filtered_argmax(
                    &self.total_forward_distance,
                    &self.lower_bound_forward_eccentricities,
                    |i, _| self.incomplete_forward_vertex(i),
                );
                pl.info(format_args!(
                    "Performing forward SumSweep visit from {:?}.",
                    v
                ));
                self.step_sum_sweep(v, true, pl.clone())
                    .with_context(|| format!("Could not perform forward visit from {:?}", v))?;
            }
        }

        Ok(())
    }

    /// Computes diameter, radius, and/or all eccentricities.
    ///
    /// Results can be accessed by methods [`Self::radius`], [`Self::diameter`], [`Self::radial_vertex`],
    /// [`Self::diametral_vertex`], [`Self::eccentricity`].
    ///
    /// # Arguments
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    pub fn compute(&mut self, mut pl: impl ProgressLog) -> Result<()> {
        if self.number_of_nodes == 0 {
            return Ok(());
        }
        pl.start("Computing SumSweep...");

        if self.compute_radial_vertices {
            self.compute_radial_vertices(pl.clone())
                .with_context(|| "Could not compute radial vertices")?;
        }

        let max_outdegree_vertex = AtomicUsize::new(0);

        self.threadpool.borrow().install(|| {
            (0..self.number_of_nodes).into_par_iter().for_each(|v| {
                let outdegree = self.graph.outdegree(v);
                let mut current_max = max_outdegree_vertex.load(Ordering::Relaxed);
                while outdegree > self.graph.outdegree(current_max) {
                    let result = max_outdegree_vertex.compare_exchange(
                        current_max,
                        v,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    );
                    if result.is_ok() {
                        break;
                    }
                    current_max = max_outdegree_vertex.load(Ordering::Relaxed);
                }
            });
        });

        self.sum_sweep_heuristic(max_outdegree_vertex.load(Ordering::Relaxed), 6, pl.clone())
            .with_context(|| "Could not perform first 6 iterations of SumSweep heuristic.")?;

        let mut points = [self.graph.num_nodes() as f64; 5];
        let mut missing_nodes = self
            .find_missing_nodes(pl.clone())
            .with_context(|| "Could not compute missing nodes")?;
        let mut old_missing_nodes;

        pl.info(format_args!(
            "Missing nodes: {} out of {}",
            missing_nodes,
            self.number_of_nodes * 2
        ));

        while missing_nodes > 0 {
            let step_to_perform =
                math::argmax(&points).with_context(|| "Could not find step to perform")?;

            match step_to_perform {
                0 => {
                    pl.info(format_args!("Performing all_cc_upper_bound."));
                    let pivot = self
                        .find_best_pivot(pl.clone())
                        .with_context(|| "Could not find best pivot for allCCUpperBound")?;
                    self.all_cc_upper_bound(pivot, pl.clone())
                        .with_context(|| "Could not perform allCCUpperBound")?
                }
                1 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex maximizing the upper bound."
                    ));
                    let v = math::filtered_argmax(
                        &self.upper_bound_forward_eccentricities,
                        &self.total_forward_distance,
                        |i, _| self.incomplete_forward_vertex(i),
                    );
                    self.step_sum_sweep(v, true, pl.clone())
                        .with_context(|| format!("Could not perform forward visit from {:?}", v))?
                }
                2 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex minimizing the lower bound."
                    ));
                    let v = math::filtered_argmin(
                        &self.lower_bound_forward_eccentricities,
                        &self.total_forward_distance,
                        |i, _| self.radial_vertices[i],
                    );
                    self.step_sum_sweep(v, true, pl.clone())
                        .with_context(|| format!("Could not perform forward visit from {:?}", v))?
                }
                3 => {
                    pl.info(format_args!(
                        "Performing a backward BFS from a vertex maximizing the upper bound."
                    ));
                    let v = math::filtered_argmax(
                        &self.upper_bound_backward_eccentricities,
                        &self.total_backward_distance,
                        |i, _| self.incomplete_backward_vertex(i),
                    );
                    self.step_sum_sweep(v, false, pl.clone()).with_context(|| {
                        format!("Could not perform backwards visit from {:?}", v)
                    })?
                }
                4 => {
                    pl.info(format_args!(
                        "Performing a backward BFS, from a vertex maximizing the distance sum."
                    ));
                    let v = math::filtered_argmax(
                        &self.total_backward_distance,
                        &self.upper_bound_backward_eccentricities,
                        |i, _| self.incomplete_backward_vertex(i),
                    );
                    self.step_sum_sweep(v, false, pl.clone()).with_context(|| {
                        format!("Could not perform backwards visit from {:?}", v)
                    })?
                }
                5.. => panic!(),
            }

            old_missing_nodes = missing_nodes;
            missing_nodes = self
                .find_missing_nodes(pl.clone())
                .with_context(|| "Could not compute missing nodes")?;
            points[step_to_perform] = (old_missing_nodes - missing_nodes) as f64;

            // This is to make rust-analyzer happy as it cannot recognize mut reference
            #[allow(clippy::needless_range_loop)]
            for i in 0..points.len() {
                if i != step_to_perform && points[i] >= 0.0 {
                    points[i] += 2.0 / self.iterations as f64;
                }
            }

            pl.info(format_args!(
                "Missing nodes: {} out of {}",
                missing_nodes,
                self.number_of_nodes * 2
            ));
        }

        if self.output == SumSweepOutputLevel::Radius
            || self.output == SumSweepOutputLevel::RadiusDiameter
        {
            pl.info(format_args!(
                "Radius: {} ({} iterations).",
                self.radius_upper_bound,
                self.radius_iterations
                    .expect("radius iterations should not be None")
            ));
        }
        if self.output == SumSweepOutputLevel::Diameter
            || self.output == SumSweepOutputLevel::RadiusDiameter
        {
            pl.info(format_args!(
                "Diameter: {} ({} iterations).",
                self.diameter_lower_bound,
                self.diameter_iterations
                    .expect("radius iterations should not be None"),
            ));
        }
        pl.done();

        Ok(())
    }

    /// Returns the radius of the graph if it has already been computed, [`None`] otherwise.
    pub fn radius(&self) -> Option<usize> {
        if self.radius_iterations.is_none() {
            None
        } else {
            Some(self.radius_upper_bound)
        }
    }

    /// Returns the diameter of the graph if is has already been computed, [`None`] otherwise.
    pub fn diameter(&self) -> Option<usize> {
        if self.diameter_iterations.is_none() {
            None
        } else {
            Some(self.diameter_lower_bound)
        }
    }

    /// Returns a radial vertex if it has already been computed, [`None`] otherwise.
    pub fn radial_vertex(&self) -> Option<usize> {
        if self.radius_iterations.is_none() {
            None
        } else {
            Some(self.radius_vertex)
        }
    }

    /// Returns a diametral vertex if it has already been computed, [`None`] otherwise.
    pub fn diametral_vertex(&self) -> Option<usize> {
        if self.diameter_iterations.is_none() {
            None
        } else {
            Some(self.diameter_vertex)
        }
    }

    /// Returns the eccentricity of a vertex if it has already been computed, [`None`] otherwise.
    ///
    /// # Arguments
    /// * `vertex`: The vertex.
    /// * `forward`: Whether to return the forward eccentricity (if `true`) or the backward
    ///   eccentricity (if `false`).
    pub fn eccentricity(&self, vertex: usize, forward: bool) -> Option<usize> {
        if forward {
            self.forward_eccentricity(vertex)
        } else {
            self.backward_eccentricity(vertex)
        }
    }

    /// Returns the number of iterations needed to compute the radius if it has already
    /// been computed, [`None`] otherwise.
    pub fn radius_iterations(&self) -> Option<usize> {
        self.radius_iterations.map(|v| v.into())
    }

    /// Returns the number of iterations needed to compute the diameter if it has already
    /// been computed, [`None`] otherwise.
    pub fn diameter_iterations(&self) -> Option<usize> {
        self.diameter_iterations.map(|v| v.into())
    }

    /// Returns the number of iterations needed to compute all forward eccentricities
    /// if they have already been computed, [`None`] otherwise.
    pub fn all_forward_iterations(&self) -> Option<usize> {
        self.forward_eccentricities_iterations.map(|v| v.into())
    }

    /// Returns the number of iterations needed to compute all eccentricities if they
    /// have already been computed, [`None`] otherwise.
    pub fn all_iterations(&self) -> Option<usize> {
        self.all_eccentricities_iterations.map(|v| v.into())
    }

    /// Uses a heuristic to decide which is the best pivot to choose in each strongly connected
    /// component, in order to perform the [`Self::all_cc_upper_bound`] method.
    ///
    /// # Arguments
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn find_best_pivot(&self, mut pl: impl ProgressLog) -> Result<Vec<usize>> {
        debug_assert!(self.number_of_nodes < usize::MAX);

        let mut pivot: Vec<Option<NonMaxUsize>> =
            vec![None; self.strongly_connected_components.number_of_components()];
        let components = self.strongly_connected_components.component();
        pl.expected_updates(Some(components.len()));
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.start("Computing best pivot");

        for (v, &component) in components.iter().enumerate().rev() {
            if let Some(p) = pivot[component] {
                let p = p.into();
                let current = self.lower_bound_backward_eccentricities[v]
                    + self.lower_bound_forward_eccentricities[v]
                    + if self.incomplete_forward_vertex(v) {
                        0
                    } else {
                        self.number_of_nodes
                    }
                    + if self.incomplete_backward_vertex(v) {
                        0
                    } else {
                        self.number_of_nodes
                    };

                let best = self.lower_bound_backward_eccentricities[p]
                    + self.lower_bound_forward_eccentricities[p]
                    + if self.incomplete_forward_vertex(p) {
                        0
                    } else {
                        self.number_of_nodes
                    }
                    + if self.incomplete_backward_vertex(p) {
                        0
                    } else {
                        self.number_of_nodes
                    };

                if current < best
                    || (current == best
                        && self.total_forward_distance[v] + self.total_backward_distance[v]
                            <= self.total_forward_distance[p] + self.total_backward_distance[p])
                {
                    pivot[component] = NonMaxUsize::new(v);
                }
            } else {
                pivot[component] = NonMaxUsize::new(v);
            }
            pl.light_update();
        }

        pl.done();

        Ok(pivot.into_iter().map(|x| x.unwrap().into()).collect())
    }

    /// Computes and stores in variable [`Self::radial_vertices`] the set of vertices that are
    /// either in the biggest strongly connected component or that are able to reach vertices in
    /// the biggest strongly connected component.
    ///
    /// # Arguments
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn compute_radial_vertices(&mut self, mut pl: impl ProgressLog) -> Result<()> {
        if self.number_of_nodes == 0 {
            return Ok(());
        }

        pl.expected_updates(None);
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.start("Computing radial vertices...");

        let component = self.strongly_connected_components.component();
        let scc_sizes = self.strongly_connected_components.compute_sizes();
        let max_size_scc =
            math::argmax(&scc_sizes).with_context(|| "Could not find max size scc.")?;

        pl.info(format_args!(
            "Searching for biggest strongly connected component"
        ));

        let mut v = self.number_of_nodes;

        while v > 0 {
            v -= 1;
            if component[v] == max_size_scc {
                break;
            }
        }

        pl.info(format_args!("Computing radial vertices set"));

        self.transposed_visit
            .visit_from_node(
                |args| {
                    self.radial_vertices
                        .set(args.node_index, true, Ordering::Relaxed)
                },
                v,
                &mut pl,
            )
            .with_context(|| format!("Could not perform BFS from {}", v))?;
        self.transposed_visit
            .reset()
            .with_context(|| "Could not reset transposed visit")?;

        pl.done();

        Ok(())
    }

    /// Performs a (forward or backward) BFS, updating lower bounds on the eccentricities
    /// of all visited vertices.
    ///
    /// # Arguments
    /// * `start`: The starting vertex of the BFS. If [`None`], no visit happens.
    /// * `forward`: Whether the BFS is performed following the direction of edges or
    ///   in the opposite direction.
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn step_sum_sweep(
        &mut self,
        start: Option<usize>,
        forward: bool,
        pl: impl ProgressLog,
    ) -> Result<()> {
        if let Some(start) = start {
            if forward {
                self.forward_step_sum_sweep(start, pl)
                    .with_context(|| format!("Cannot perform forward visit from {}", start))?;
            } else {
                self.backwards_step_sum_sweep(start, pl)
                    .with_context(|| format!("Cannot perform backwards visit from {}", start))?;
            }
            self.iterations += 1;
        }
        Ok(())
    }

    #[inline(always)]
    fn backwards_step_sum_sweep(&mut self, start: usize, mut pl: impl ProgressLog) -> Result<()> {
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.expected_updates(None);
        pl.start(format!("Performing backwards BFS starting from {}", start));

        let max_dist = AtomicUsize::new(0);
        let radius = RwLock::new((self.radius_upper_bound, self.radius_vertex));

        let lower_bound_forward_eccentricities = self
            .lower_bound_forward_eccentricities
            .as_mut_slice_of_cells();
        let total_forward_distance = self.total_forward_distance.as_mut_slice_of_cells();

        self.transposed_visit
            .visit_from_node(
                |args| {
                    let (distance, node) = (args.distance_from_root, args.node_index);
                    // Safety for unsafe blocks: each node gets accessed exactly once, so no data races can happen
                    max_dist.fetch_max(distance, Ordering::Relaxed);

                    let node_forward_lower_bound_ptr =
                        unsafe { lower_bound_forward_eccentricities.get_mut_unsafe(node) };
                    let node_total_forward_distance_ptr =
                        unsafe { total_forward_distance.get_mut_unsafe(node) };

                    let node_forward_lower_bound = unsafe { *node_forward_lower_bound_ptr };
                    let node_forward_upper_bound = self.upper_bound_forward_eccentricities[node];

                    unsafe {
                        *node_total_forward_distance_ptr += distance;
                    }
                    if node_forward_lower_bound != node_forward_upper_bound
                        && node_forward_lower_bound < distance
                    {
                        unsafe {
                            *node_forward_lower_bound_ptr = distance;
                        }

                        if distance == node_forward_upper_bound && self.radial_vertices[node] {
                            let mut update_radius = false;
                            {
                                let radius_lock = radius.read().unwrap();
                                if distance < radius_lock.0 {
                                    update_radius = true;
                                }
                            }

                            if update_radius {
                                let mut radius_lock = radius.write().unwrap();
                                if distance < radius_lock.0 {
                                    radius_lock.0 = distance;
                                    radius_lock.1 = node;
                                }
                            }
                        }
                    }
                },
                start,
                &mut pl,
            )
            .with_context(|| format!("Could not perform BFS from {}", start))?;
        self.transposed_visit
            .reset()
            .with_context(|| "Could not reset transposed visit")?;

        let ecc_start = max_dist.load(Ordering::Relaxed);

        self.lower_bound_backward_eccentricities[start] = ecc_start;
        self.upper_bound_backward_eccentricities[start] = ecc_start;

        (self.radius_upper_bound, self.radius_vertex) = radius.into_inner().unwrap();

        if self.diameter_lower_bound < ecc_start {
            self.diameter_lower_bound = ecc_start;
            self.diameter_vertex = start;
        }

        pl.done();

        Ok(())
    }

    #[inline(always)]
    fn forward_step_sum_sweep(&mut self, start: usize, mut pl: impl ProgressLog) -> Result<()> {
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.expected_updates(None);
        pl.start(format!("Performing forward BFS starting from {}", start));

        let max_dist = AtomicUsize::new(0);

        let lower_bound_backward_eccentricities = self
            .lower_bound_backward_eccentricities
            .as_mut_slice_of_cells();
        let total_backward_distance = self.total_backward_distance.as_mut_slice_of_cells();

        self.visit
            .visit_from_node(
                |args| {
                    let (distance, node) = (args.distance_from_root, args.node_index);
                    // Safety for unsafe blocks: each node gets accessed exactly once, so no data races can happen
                    max_dist.fetch_max(distance, Ordering::Relaxed);

                    let node_backward_lower_bound_ptr =
                        unsafe { lower_bound_backward_eccentricities.get_mut_unsafe(node) };
                    let node_total_backward_distance_ptr =
                        unsafe { total_backward_distance.get_mut_unsafe(node) };

                    let node_backward_lower_bound = unsafe { *node_backward_lower_bound_ptr };
                    let node_backward_upper_bound = self.upper_bound_backward_eccentricities[node];

                    unsafe {
                        *node_total_backward_distance_ptr += distance;
                    }
                    if node_backward_lower_bound != node_backward_upper_bound
                        && node_backward_lower_bound < distance
                    {
                        unsafe {
                            *node_backward_lower_bound_ptr = distance;
                        }
                    }
                },
                start,
                &mut pl,
            )
            .with_context(|| format!("Could not perform BFS from {}", start))?;
        self.visit
            .reset()
            .with_context(|| "Could not reset visit")?;

        let ecc_start = max_dist.load(Ordering::Relaxed);

        self.lower_bound_forward_eccentricities[start] = ecc_start;
        self.upper_bound_forward_eccentricities[start] = ecc_start;

        if self.diameter_lower_bound < ecc_start {
            self.diameter_lower_bound = ecc_start;
            self.diameter_vertex = start;
        }
        if self.radial_vertices[start] && self.radius_upper_bound > ecc_start {
            self.radius_upper_bound = ecc_start;
            self.radius_vertex = start;
        }

        pl.done();

        Ok(())
    }

    /// Performs a (forward or backward) BFS inside each strongly connected component, starting
    /// from the pivot.
    ///
    /// # Arguments
    /// * `pivot`: An array containing in position `i` the pivot of the `i`-th strongly connected
    ///   component.
    /// * `forward`: Whether the BFS is performed following the direction of edges or
    ///   in the opposite direction.
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    ///
    /// # Return
    /// Two arrays.
    ///
    /// The first one contains the distance of each vertex from the pivot of its strongly connected
    /// component, while the second one contains in position `i` the eccentricity of the pivot of the
    /// `i`-th strongly connected component.
    fn compute_dist_pivot(
        &self,
        pivot: &[usize],
        forward: bool,
        mut pl: impl ProgressLog,
    ) -> Result<(Vec<usize>, Vec<usize>)> {
        pl.expected_updates(None);
        pl.display_memory(false);

        let (dist_pivot, usize_ecc_pivot) = if forward {
            pl.start("Computing forward dist pivots");
            self.compute_dist_pivot_from_graph(pivot, self.graph)
                .with_context(|| "Could not compute forward dist pivots")?
        } else {
            pl.start("Computing backwards dist pivots");
            self.compute_dist_pivot_from_graph(pivot, self.reversed_graph)
                .with_context(|| "Could not compute backwards dist pivots")?
        };

        pl.done();

        Ok((dist_pivot, usize_ecc_pivot))
    }

    #[inline(always)]
    fn compute_dist_pivot_from_graph(
        &self,
        pivot: &[usize],
        graph: &(impl RandomAccessGraph + Sync),
    ) -> Result<(Vec<usize>, Vec<usize>)> {
        let components = self.strongly_connected_components.component();
        let ecc_pivot = closure_vec(
            || AtomicUsize::new(0),
            self.strongly_connected_components.number_of_components(),
        );
        let mut dist_pivot = vec![0; self.number_of_nodes];
        let dist_pivot_mut = dist_pivot.as_mut_slice_of_cells();
        let current_index = AtomicUsize::new(0);
        let threadpool = self.threadpool.borrow();

        self.threadpool.borrow().broadcast(|_| {
            let mut bfs =
                ParallelBreadthFirstVisitFastCB::with_threads(graph, VISIT_GRANULARITY, threadpool);
            let mut current_pivot_index = current_index.fetch_add(1, Ordering::Relaxed);

            while let Some(&p) = pivot.get(current_pivot_index) {
                let pivot_component = components[p];
                let component_ecc_pivot = &ecc_pivot[pivot_component];

                bfs.visit_from_node_filtered(
                    |args| {
                        let (distance, node) = (args.distance_from_root, args.node_index);
                        // Safety: each node is accessed exactly once
                        unsafe {
                            dist_pivot_mut.write_once(node, distance);
                        }
                        component_ecc_pivot.store(distance, Ordering::Relaxed);
                    },
                    |args| components[args.node_index] == pivot_component,
                    p,
                    &mut Option::<ProgressLogger>::None,
                )
                .unwrap_or_else(|_| panic!("Could not perform visit from {}", p));

                current_pivot_index = current_index.fetch_add(1, Ordering::Relaxed);
            }
        });

        let usize_ecc_pivot = unsafe {
            let mut clone = std::mem::ManuallyDrop::new(ecc_pivot);
            Vec::from_raw_parts(
                clone.as_mut_ptr() as *mut usize,
                clone.len(),
                clone.capacity(),
            )
        };

        Ok((dist_pivot, usize_ecc_pivot))
    }

    /// Performs a step of the ExactSumSweep algorithm.
    ///
    /// # Arguments
    /// * `pivot`: An array containing in position `i` the pivot of the `i`-th strongly connected component.
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn all_cc_upper_bound(&mut self, pivot: Vec<usize>, mut pl: impl ProgressLog) -> Result<()> {
        pl.item_name("elements");
        pl.display_memory(false);
        pl.expected_updates(Some(
            pivot.len()
                + self.strongly_connected_components.number_of_components()
                + self.number_of_nodes,
        ));
        pl.start("Performing AllCCUpperBound step of ExactSumSweep algorithm");

        let dist_ecc_f = self
            .compute_dist_pivot(&pivot, true, pl.clone())
            .with_context(|| "Could not compute forward dist pivot")?;
        let dist_ecc_b = self
            .compute_dist_pivot(&pivot, false, pl.clone())
            .with_context(|| "Could not compute backward dist pivot")?;
        let dist_pivot_f = dist_ecc_f.0;
        let mut ecc_pivot_f = dist_ecc_f.1;
        let dist_pivot_b = dist_ecc_b.0;
        let mut ecc_pivot_b = dist_ecc_b.1;
        let components = self.strongly_connected_components.component();

        // Tarjan's algorithm emits components in reverse topological order.
        // In order to bound forward eccentricities in reverse topological order the components
        // are traversed as is.
        for (c, &p) in pivot.iter().enumerate() {
            for connection in self.strongly_connected_components_graph.children(c) {
                let next_c = connection.target;
                let start = connection.start;
                let end = connection.end;

                ecc_pivot_f[c] = std::cmp::max(
                    ecc_pivot_f[c],
                    dist_pivot_f[start] + 1 + dist_pivot_b[end] + ecc_pivot_f[next_c],
                );

                if ecc_pivot_f[c] >= self.upper_bound_forward_eccentricities[p] {
                    ecc_pivot_f[c] = self.upper_bound_forward_eccentricities[p];
                    break;
                }
            }
            pl.light_update();
        }

        // Tarjan's algorithm emits components in reverse topological order.
        // In order to bound backward eccentricities in topological order the components order
        // must be reversed.
        for c in (0..self.strongly_connected_components.number_of_components()).rev() {
            for component in self.strongly_connected_components_graph.children(c) {
                let next_c = component.target;
                let start = component.start;
                let end = component.end;

                ecc_pivot_b[next_c] = std::cmp::max(
                    ecc_pivot_b[next_c],
                    dist_pivot_f[start] + 1 + dist_pivot_b[end] + ecc_pivot_b[c],
                );

                if ecc_pivot_b[next_c] >= self.upper_bound_backward_eccentricities[pivot[next_c]] {
                    ecc_pivot_b[next_c] = self.upper_bound_backward_eccentricities[pivot[next_c]];
                }
            }
            pl.light_update();
        }

        let radius = RwLock::new((self.radius_upper_bound, self.radius_vertex));

        let upper_bound_forward_eccentricities = self
            .upper_bound_forward_eccentricities
            .as_mut_slice_of_cells();
        let upper_bound_backward_eccentricities = self
            .upper_bound_backward_eccentricities
            .as_mut_slice_of_cells();

        self.threadpool.borrow().install(|| {
            (0..self.number_of_nodes).into_par_iter().for_each(|node| {
                // Safety for unsafe blocks: each node gets accessed exactly once, so no data races can happen
                unsafe {
                    upper_bound_forward_eccentricities.write_once(
                        node,
                        std::cmp::min(
                            upper_bound_forward_eccentricities[node].read(),
                            dist_pivot_b[node] + ecc_pivot_f[components[node]],
                        ),
                    );
                }

                if upper_bound_forward_eccentricities[node].read()
                    == self.lower_bound_forward_eccentricities[node]
                {
                    let new_ecc = upper_bound_forward_eccentricities[node].read();

                    if self.radial_vertices[node] {
                        let mut update_radius = false;
                        {
                            let radius_lock = radius.read().unwrap();
                            if new_ecc < radius_lock.0 {
                                update_radius = true;
                            }
                        }

                        if update_radius {
                            let mut radius_lock = radius.write().unwrap();
                            if new_ecc < radius_lock.0 {
                                radius_lock.0 = new_ecc;
                                radius_lock.1 = node;
                            }
                        }
                    }
                }

                unsafe {
                    upper_bound_backward_eccentricities.write_once(
                        node,
                        std::cmp::min(
                            upper_bound_backward_eccentricities[node].read(),
                            dist_pivot_f[node] + ecc_pivot_b[components[node]],
                        ),
                    );
                }
            });
        });

        pl.update_with_count(self.number_of_nodes);

        (self.radius_upper_bound, self.radius_vertex) = radius.into_inner().unwrap();

        self.iterations += 3;

        pl.done();

        Ok(())
    }

    /// Computes how many nodes are still to be processed, before outputting the result.
    ///
    /// # Arguments
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn find_missing_nodes(&mut self, mut pl: impl ProgressLog) -> Result<usize> {
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.expected_updates(Some(self.number_of_nodes));
        pl.start("Computing missing nodes");

        let (missing_r, missing_df, missing_db, missing_all_forward, missing_all_backward) =
            self.threadpool.borrow().install(|| {
                (0..self.number_of_nodes)
                    .into_par_iter()
                    .fold(
                        || (0, 0, 0, 0, 0),
                        |mut acc, node| {
                            if self.incomplete_forward_vertex(node) {
                                acc.3 += 1;
                                if self.upper_bound_forward_eccentricities[node]
                                    > self.diameter_lower_bound
                                {
                                    acc.1 += 1;
                                }
                                if self.radial_vertices[node]
                                    && self.lower_bound_forward_eccentricities[node]
                                        < self.radius_upper_bound
                                {
                                    acc.0 += 1;
                                }
                            }
                            if self.incomplete_backward_vertex(node) {
                                acc.4 += 1;
                                if self.upper_bound_backward_eccentricities[node]
                                    > self.diameter_lower_bound
                                {
                                    acc.2 += 1;
                                }
                            }
                            acc
                        },
                    )
                    .reduce(
                        || (0, 0, 0, 0, 0),
                        |acc, elem| {
                            (
                                acc.0 + elem.0,
                                acc.1 + elem.1,
                                acc.2 + elem.2,
                                acc.3 + elem.3,
                                acc.4 + elem.4,
                            )
                        },
                    )
            });

        pl.update_with_count(self.number_of_nodes);

        let iterations =
            NonMaxUsize::new(self.iterations).expect("Iterations should never be usize::MAX");

        if missing_r == 0 && self.radius_iterations.is_none() {
            self.radius_iterations = Some(iterations);
        }
        if (missing_df == 0 || missing_db == 0) && self.diameter_iterations.is_none() {
            self.diameter_iterations = Some(iterations);
        }
        if missing_all_forward == 0 && self.forward_eccentricities_iterations.is_none() {
            self.forward_eccentricities_iterations = Some(iterations);
        }
        if missing_all_forward == 0 && missing_all_backward == 0 {
            self.all_eccentricities_iterations = Some(iterations);
        }

        pl.done();

        Ok(match self.output {
            SumSweepOutputLevel::Radius => missing_r,
            SumSweepOutputLevel::Diameter => std::cmp::min(missing_df, missing_db),
            SumSweepOutputLevel::RadiusDiameter => {
                missing_r + std::cmp::min(missing_df, missing_db)
            }
            SumSweepOutputLevel::AllForward => missing_all_forward,
            SumSweepOutputLevel::All => missing_all_backward + missing_all_forward,
        })
    }
}
