use crate::{
    algo::{
        diameter::*,
        scc::TarjanStronglyConnectedComponents,
        visits::{
            breadth_first::{Event, ParFair},
            Node, Parallel,
        },
    },
    prelude::*,
    utils::Threads,
};
use dsi_progress_logger::ProgressLog;
use std::borrow::Borrow;
use std::convert::Infallible;
use webgraph::traits::RandomAccessGraph;

/// Builder for [`SumSweepUndirectedDiameterRadius`].
pub struct SumSweepUndirectedDiameterRadiusBuilder<
    'a,
    G: RandomAccessGraph + Sync,
    T,
    C: StronglyConnectedComponents,
> {
    graph: &'a G,
    output: SumSweepOutputLevel,
    threads: T,
    _marker: std::marker::PhantomData<C>,
}

impl<'a, G: RandomAccessGraph + Sync>
    SumSweepUndirectedDiameterRadiusBuilder<'a, G, Threads, TarjanStronglyConnectedComponents>
{
    pub fn new(graph: &'a G, output: SumSweepOutputLevel) -> Self {
        let output = match output {
            SumSweepOutputLevel::Radius => SumSweepOutputLevel::Radius,
            SumSweepOutputLevel::Diameter => SumSweepOutputLevel::Diameter,
            SumSweepOutputLevel::RadiusDiameter => SumSweepOutputLevel::RadiusDiameter,
            _ => SumSweepOutputLevel::All,
        };
        Self {
            graph,
            output,
            threads: Threads::Default,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, G: RandomAccessGraph + Sync, C: StronglyConnectedComponents, T>
    SumSweepUndirectedDiameterRadiusBuilder<'a, G, T, C>
{
    /// Sets the [`SumSweepUndirectedDiameterRadius`] instance to use the default [`rayon::ThreadPool`].
    pub fn default_threadpool(self) -> SumSweepUndirectedDiameterRadiusBuilder<'a, G, Threads, C> {
        SumSweepUndirectedDiameterRadiusBuilder {
            graph: self.graph,
            output: self.output,
            threads: Threads::Default,
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
            _marker: self._marker,
        }
    }

    /// Sets the algorithm to use to compute the strongly connected components for the graph.
    pub fn scc<C2: StronglyConnectedComponents>(
        self,
    ) -> SumSweepUndirectedDiameterRadiusBuilder<'a, G, T, C2> {
        SumSweepUndirectedDiameterRadiusBuilder {
            graph: self.graph,
            output: self.output,
            threads: self.threads,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, G: RandomAccessGraph + Sync, C: StronglyConnectedComponents + Sync>
    SumSweepUndirectedDiameterRadiusBuilder<'a, G, Threads, C>
{
    /// Builds the [`SumSweepUndirectedDiameterRadius`] instance with the specified settings and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// * `pl`: A progress logger.
    pub fn build(
        self,
        pl: &mut impl ProgressLog,
    ) -> SumSweepUndirectedDiameterRadius<
        'a,
        G,
        C,
        ParFair<Node, Infallible, &'a G, rayon::ThreadPool>,
        rayon::ThreadPool,
    > {
        let mut builder =
            SumSweepDirectedDiameterRadiusBuilder::new(self.graph, self.graph, self.output)
                .scc::<C>();
        builder = match self.threads {
            Threads::Default => builder.default_threadpool(),
            Threads::NumThreads(num_threads) => builder.num_threads(num_threads),
        };
        SumSweepUndirectedDiameterRadius {
            inner: builder.build(pl),
        }
    }
}

impl<
        'a,
        G: RandomAccessGraph + Sync,
        C: StronglyConnectedComponents + Sync,
        T: Borrow<rayon::ThreadPool> + Clone + Sync,
    > SumSweepUndirectedDiameterRadiusBuilder<'a, G, T, C>
{
    /// Builds the [`SumSweepUndirectedDiameterRadius`] instance with the specified settings and
    /// logs progress with the provided logger.
    ///
    /// # Arguments
    /// * `pl`: A progress logger.
    pub fn build(
        self,
        pl: &mut impl ProgressLog,
    ) -> SumSweepUndirectedDiameterRadius<'a, G, C, ParFair<Node, Infallible, &'a G, T>, T> {
        let builder =
            SumSweepDirectedDiameterRadiusBuilder::new(self.graph, self.graph, self.output)
                .scc::<C>()
                .threadpool(self.threads);
        SumSweepUndirectedDiameterRadius {
            inner: builder.build(pl),
        }
    }
}

/// The implementation of the *SumSweep* algorithm on undirected graphs.
///
/// The algorithm is started by calling [`Self::compute`] with a progress logger
/// if desired.
///
/// Results can be accessed with methods [`Self::radius`], [`Self::diameter`],
/// [`Self::radial_vertex`], [`Self::diametral_vertex`] and [`Self::eccentricity`].
///
/// Information on the number of iterations may be retrieved with [`Self::radius_iterations`],
/// [`Self::diameter_iterations`] and [`Self::all_iterations`].
///
/// *Implementation detail*: this is just a wrapper to the [`directed version`](SumSweepDirectedDiameterRadius)
/// using the provided graph as both the direct and the transposed version,
/// as it is actually faster than the original algorithm for undirected graphs.
pub struct SumSweepUndirectedDiameterRadius<
    'a,
    G: RandomAccessGraph + Sync,
    C: StronglyConnectedComponents + Sync,
    V: Parallel<Event<Node>, Infallible> + Sync,
    T: Borrow<rayon::ThreadPool> + Sync,
> {
    inner: SumSweepDirectedDiameterRadius<'a, G, G, C, V, V, T>,
}

impl<'a, G, C, V, T> SumSweepUndirectedDiameterRadius<'a, G, C, V, T>
where
    G: RandomAccessGraph + Sync,
    C: StronglyConnectedComponents + Sync,
    V: Parallel<Event<Node>, Infallible> + Sync,
    T: Borrow<rayon::ThreadPool> + Sync,
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
    /// * `pl`: A progress logger.
    #[inline(always)]
    pub fn compute(&mut self, pl: &mut impl ProgressLog) {
        self.inner.compute(pl)
    }
}
