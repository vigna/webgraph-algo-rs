use crate::{
    algo::{
        diameter::*,
        scc::TarjanStronglyConnectedComponents,
        visits::{
            breadth_first::{Event, ParFair},
            Parallel,
        },
    },
    prelude::*,
    utils::check_symmetric,
};
use dsi_progress_logger::ProgressLog;
use rayon::ThreadPool;
use webgraph::traits::RandomAccessGraph;

/// The implementation of the *ExactSumSweep* algorithm on undirected graphs.
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
/// *Implementation detail*: this is just a wrapper to the [`directed version`](DirExactSumSweedDirExactSumSweep)
/// using the provided graph as both the direct and the transposed version,
/// as it is actually faster than the original algorithm for undirected graphs.
pub struct UndirExactSumSweep<
    'a,
    G: RandomAccessGraph + Sync,
    C: StronglyConnectedComponents + Sync,
    V: Parallel<Event> + Sync,
> {
    inner: DirExactSumSweep<'a, G, G, C, V, V>,
}

impl<'a, G: RandomAccessGraph + Sync>
    UndirExactSumSweep<'a, G, TarjanStronglyConnectedComponents, ParFair<&'a G>>
{
    /// Build a new instance to compute the *ExactSumSweep* algorithm on undirected graphs.
    ///
    /// # Arguments
    /// * `graph`: the undirected graph.
    /// * `output`: the desired output of the algorithm.
    /// * `pl`: a progress logger.
    pub fn new(graph: &'a G, output: OutputLevel, pl: &mut impl ProgressLog) -> Self {
        debug_assert!(check_symmetric(graph), "graph should be symmetric");
        let output = match output {
            OutputLevel::Radius => OutputLevel::Radius,
            OutputLevel::Diameter => OutputLevel::Diameter,
            OutputLevel::RadiusDiameter => OutputLevel::RadiusDiameter,
            _ => OutputLevel::AllForward,
        };
        Self {
            inner: DirExactSumSweep::new(graph, graph, output, None, pl),
        }
    }
}

impl<'a, G, C, V> UndirExactSumSweep<'a, G, C, V>
where
    G: RandomAccessGraph + Sync,
    C: StronglyConnectedComponents + Sync,
    V: Parallel<Event> + Sync,
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
        self.inner.eccentricity(vertex, true)
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

    /// Computes diameter, radius, and/or all eccentricities.
    ///
    /// Results can be accessed by methods [`Self::radius`], [`Self::diameter`], [`Self::radial_vertex`],
    /// [`Self::diametral_vertex`], [`Self::eccentricity`].
    ///
    /// # Arguments
    /// * `thread_pool`: The thread_pool to use for parallel computation.
    /// * `pl`: A progress logger.
    #[inline(always)]
    pub fn compute(&mut self, thread_pool: &ThreadPool, pl: &mut impl ProgressLog) {
        self.inner.compute(thread_pool, pl)
    }
}
