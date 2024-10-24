use crate::{
    algo::{
        bfv::ParallelBreadthFirstVisitFastCB,
        diameter::{
            SumSweepDirectedDiameterRadius, SumSweepDirectedDiameterRadiusBuilder,
            SumSweepOutputLevel,
        },
        scc::TarjanStronglyConnectedComponents,
    },
    prelude::*,
    utils::Threads,
};
use anyhow::{Context, Result};
use dsi_progress_logger::ProgressLog;
use std::borrow::Borrow;
use webgraph::traits::RandomAccessGraph;

/// Builder for [`SumSweepUndirectedDiameterRadius`].
pub struct SumSweepUndirectedDiameterRadiusBuilder<
    'a,
    G: RandomAccessGraph + Sync,
    T,
    C: StronglyConnectedComponents<G>,
> {
    graph: &'a G,
    output: SumSweepOutputLevel,
    threads: T,
    mem_options: TempMmapOptions,
    _marker: std::marker::PhantomData<C>,
}

impl<'a, G: RandomAccessGraph + Sync>
    SumSweepUndirectedDiameterRadiusBuilder<'a, G, Threads, TarjanStronglyConnectedComponents<G>>
{
    pub fn new(graph: &'a G, output: SumSweepOutputLevel) -> Self {
        let output = match output {
            SumSweepOutputLevel::Radius => SumSweepOutputLevel::Radius,
            SumSweepOutputLevel::Diameter => SumSweepOutputLevel::Diameter,
            _ => SumSweepOutputLevel::All,
        };
        Self {
            graph,
            output,
            threads: Threads::Default,
            mem_options: TempMmapOptions::Default,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, G: RandomAccessGraph + Sync, C: StronglyConnectedComponents<G>, T>
    SumSweepUndirectedDiameterRadiusBuilder<'a, G, T, C>
{
    /// Sets the memory options used by the support arrays of the
    /// [`SumSweepUndirectedDiameterRadius`] instance.
    ///
    /// # Argumets
    /// * `settings`: the new settings to use.
    pub fn mem_settings(mut self, settings: TempMmapOptions) -> Self {
        self.mem_options = settings;
        self
    }

    /// Sets the [`SumSweepUndirectedDiameterRadius`] instance to use the default [`rayon::ThreadPool`].
    pub fn default_threadpool(self) -> SumSweepUndirectedDiameterRadiusBuilder<'a, G, Threads, C> {
        SumSweepUndirectedDiameterRadiusBuilder {
            graph: self.graph,
            output: self.output,
            threads: Threads::Default,
            mem_options: self.mem_options,
            _marker: self._marker,
        }
    }

    /// Sets the [`SumSweepUndirectedDiameterRadius`] instance to use a custom [`rayon::ThreadPool`] with the
    /// specified number of threads.
    ///
    /// # Arguments
    /// * `num_threads`: the number of threads to use for the new `ThreadPool`.
    pub fn num_threads(
        self,
        num_threads: usize,
    ) -> SumSweepUndirectedDiameterRadiusBuilder<'a, G, Threads, C> {
        SumSweepUndirectedDiameterRadiusBuilder {
            graph: self.graph,
            output: self.output,
            threads: Threads::NumThreads(num_threads),
            mem_options: self.mem_options,
            _marker: self._marker,
        }
    }

    /// Sets the [`SumSweepUndirectedDiameterRadius`] instance to use the provided [`rayon::ThreadPool`].
    ///
    /// # Arguments
    /// * `threadpool`: the custom `ThreadPool` to use.
    pub fn threadpool<T2: Borrow<rayon::ThreadPool> + Clone + Sync>(
        self,
        threads: T2,
    ) -> SumSweepUndirectedDiameterRadiusBuilder<'a, G, T2, C> {
        SumSweepUndirectedDiameterRadiusBuilder {
            graph: self.graph,
            output: self.output,
            threads,
            mem_options: self.mem_options,
            _marker: self._marker,
        }
    }

    /// Sets the algorithm to use to compute the strongly connected components for the graph.
    pub fn scc<C2: StronglyConnectedComponents<G>>(
        self,
    ) -> SumSweepUndirectedDiameterRadiusBuilder<'a, G, T, C2> {
        SumSweepUndirectedDiameterRadiusBuilder {
            graph: self.graph,
            output: self.output,
            threads: self.threads,
            mem_options: self.mem_options,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, G: RandomAccessGraph + Sync, C: StronglyConnectedComponents<G> + Sync>
    SumSweepUndirectedDiameterRadiusBuilder<'a, G, Threads, C>
{
    /// Builds the [`SumSweepUndirectedDiameterRadius`] instance with the specified settings and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the build process. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    pub fn build(
        self,
        pl: impl ProgressLog,
    ) -> Result<
        SumSweepUndirectedDiameterRadius<
            'a,
            G,
            C,
            ParallelBreadthFirstVisitFastCB<'a, G, rayon::ThreadPool>,
            rayon::ThreadPool,
        >,
    > {
        let mut builder =
            SumSweepDirectedDiameterRadiusBuilder::new(self.graph, self.graph, self.output)
                .mem_settings(self.mem_options)
                .scc::<C>();
        builder = match self.threads {
            Threads::Default => builder.default_threadpool(),
            Threads::NumThreads(num_threads) => builder.num_threads(num_threads),
        };
        Ok(SumSweepUndirectedDiameterRadius {
            inner: builder
                .build(pl)
                .with_context(|| "Could not build directed sum sweep")?,
        })
    }
}

impl<
        'a,
        G: RandomAccessGraph + Sync,
        C: StronglyConnectedComponents<G> + Sync,
        T: Borrow<rayon::ThreadPool> + Clone + Sync,
    > SumSweepUndirectedDiameterRadiusBuilder<'a, G, T, C>
{
    /// Builds the [`SumSweepUndirectedDiameterRadius`] instance with the specified settings and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the build process. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    pub fn build(
        self,
        pl: impl ProgressLog,
    ) -> Result<
        SumSweepUndirectedDiameterRadius<'a, G, C, ParallelBreadthFirstVisitFastCB<'a, G, T>, T>,
    > {
        let builder =
            SumSweepDirectedDiameterRadiusBuilder::new(self.graph, self.graph, self.output)
                .mem_settings(self.mem_options)
                .scc::<C>()
                .threadpool(self.threads);
        Ok(SumSweepUndirectedDiameterRadius {
            inner: builder
                .build(pl)
                .with_context(|| "Could not build directed sum sweep")?,
        })
    }
}

pub struct SumSweepUndirectedDiameterRadius<
    'a,
    G: RandomAccessGraph + Sync,
    C: StronglyConnectedComponents<G> + Sync,
    V: BreadthFirstGraphVisit + Sync,
    T: Borrow<rayon::ThreadPool> + Sync,
> {
    inner: SumSweepDirectedDiameterRadius<'a, G, G, C, V, V, T>,
}

impl<
        'a,
        G: RandomAccessGraph + Sync,
        C: StronglyConnectedComponents<G> + Sync,
        V: BreadthFirstGraphVisit + Sync,
        T: Borrow<rayon::ThreadPool> + Sync,
    > SumSweepUndirectedDiameterRadius<'a, G, C, V, T>
{
    /// Returns the radius of the graph if it has already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radius(&self) -> Option<usize> {
        self.inner.radius()
    }

    /// Returns the diameter of the graph if is has already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diameter(&self) -> Option<usize> {
        self.inner.diameter()
    }

    /// Returns a radial vertex if it has already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radial_vertex(&self) -> Option<usize> {
        self.inner.radial_vertex()
    }

    /// Returns a diametral vertex if it has already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diametral_vertex(&self) -> Option<usize> {
        self.inner.diametral_vertex()
    }

    /// Returns the eccentricity of a vertex if it has already been computed, [`None`] otherwise.
    ///
    /// # Arguments
    /// * `vertex`: The vertex.
    #[inline(always)]
    pub fn eccentricity(&self, vertex: usize) -> Option<usize> {
        self.vertex_eccentricity(vertex)
    }

    /// Returns the number of iterations needed to compute the radius if it has already
    /// been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radius_iterations(&self) -> Option<usize> {
        self.inner.radius_iterations()
    }

    /// Returns the number of iterations needed to compute the diameter if it has already
    /// been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diameter_iterations(&self) -> Option<usize> {
        self.inner.diameter_iterations()
    }

    /// Returns the number of iterations needed to compute all eccentricities if they
    /// have already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn all_iterations(&self) -> Option<usize> {
        self.inner.all_iterations()
    }

    #[inline(always)]
    fn vertex_eccentricity(&self, index: usize) -> Option<usize> {
        let forward = self.inner.eccentricity(index, true);
        let backward = self.inner.eccentricity(index, false);
        if forward == backward {
            forward
        } else {
            None
        }
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
    #[inline(always)]
    pub fn compute(&mut self, pl: impl ProgressLog) -> Result<()> {
        self.inner.compute(pl)
    }
}
