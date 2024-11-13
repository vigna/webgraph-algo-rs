use crate::{algo::exact_sum_sweep::*, utils::check_symmetric};
use dsi_progress_logger::ProgressLog;
use rayon::ThreadPool;
use webgraph::traits::RandomAccessGraph;

/// The results of the computation of the *ExactSumSweep* algorithm on an undirected graph.
///
/// Results can be accessed on a common interface with methods [`Self::radius`], [`Self::diameter`],
/// [`Self::radial_vertex`], [`Self::diametral_vertex`], [`Self::eccentricity`] and [`Self::eccentricities`].
///
/// Information on the number of iterations may be retrieved with [`Self::radius_iterations`],
/// [`Self::diameter_iterations`] and [`Self::all_iterations`].

/// See [`OutputLevel::All`].
pub struct All {
    /// The eccentricities
    pub eccentricities: Box<[usize]>,
    /// The diameter.
    pub diameter: usize,
    /// The radius.
    pub radius: usize,
    /// A vertex whose eccentricity equals the diameter.
    pub diametral_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    pub radial_vertex: usize,
    /// Number of iterations before the radius was found.
    pub radius_iterations: usize,
    /// Number of iterations before the diameter was found.
    pub diameter_iterations: usize,
    /// Number of iterations before all eccentricities were found.
    pub iterations: usize,
}
/// See [`OutputLevel::RadiusDiameter`].
pub struct RadiusDiameter {
    /// The diameter.
    pub diameter: usize,
    /// The radius.
    pub radius: usize,
    /// A vertex whose eccentricity equals the diameter.
    pub diametral_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    pub radial_vertex: usize,
}
/// See [`OutputLevel::Diameter`].
pub struct Diameter {
    /// The diameter.
    pub diameter: usize,
    /// The radius.
    /// A vertex whose eccentricity equals the diameter.
    pub diametral_vertex: usize,
    /// Number of iterations before the diameter was found.
    pub diameter_iterations: usize,
}
/// See [`OutputLevel::Radius`].
pub struct Radius {
    /// The radius.
    pub radius: usize,
    /// A vertex whose eccentrivity equals the radius.
    pub radial_vertex: usize,
    /// Number of iterations before the radius was found.
    pub radius_iterations: usize,
}

/// Build a new instance to compute the *ExactSumSweep* algorithm on undirected graphs
/// and returns the results.
///
/// # Arguments
/// * `graph`: the direct graph.
/// * `output`: the desired output of the algorithm.
/// * `thread_pool`: The thread pool to use for parallel computation.
/// * `pl`: a progress logger.
pub fn compute<OL: OutputLevel + Sync>(
    graph: impl RandomAccessGraph + Sync,
    thread_pool: &ThreadPool,
    pl: &mut impl ProgressLog,
) -> OL::UndirectedOutput {
    debug_assert!(check_symmetric(&graph), "graph should be symmetric");
    // All and AllForward are equivalent for undirected graphs

    let mut computer = DirExactSumSweepComputer::<OL, _, _, _, _, _>::new(&graph, &graph, None, pl);
    computer.compute(thread_pool, pl);
    OL::new_undirected(computer)
}
