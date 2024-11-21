use super::{computer::DirExactSumSweepComputer, dir_outputs, undir_outputs};
use dsi_progress_logger::ProgressLog;
use rayon::ThreadPool;
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub(super) enum Output {
    /// Compute all the eccentricities of the graph.
    ///
    /// This variant is equivalent to [`AllForward`](`Self::AllForward`) in the undirected case.
    All,
    /// Compute all the forward eccentricities of the graph.
    AllForward,
    /// Computes both the diameter and the radius of the graph.
    RadiusDiameter,
    /// Computes the diameter of the graph.
    Diameter,
    /// Computers the radius of the graph.
    Radius,
}

/// Trait used to compute the results of the *Exact Sum Sweep* algorithm.
pub trait OutputLevel {
    /// The result of the algorithm when called on directed graphs.
    type DirectedOutput;
    /// The result of the algorithm when called on undirected graphs.
    type UndirectedOutput;

    /// Build a new instance to compute the *ExactSumSweep* algorithm on
    /// the specified directed graph and returns the results.
    ///
    /// # Arguments
    /// * `graph`: the direct graph.
    /// * `transpose`: the transpose of `graph`.
    /// * `radial_vertices`: an [`AtomicBitVec`] where `v[i]` is true if node `i` is to be considered
    ///    radial vertex. If [`None`] the algorithm will use the biggest connected component.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: a progress logger.
    fn compute_directed(
        graph: impl RandomAccessGraph + Sync,
        transpose: impl RandomAccessGraph + Sync,
        radial_vertices: Option<AtomicBitVec>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::DirectedOutput;

    /// Build a new instance to compute the *ExactSumSweep* algorithm on the specified
    /// undirected graph and returns the results.
    ///
    /// # Arguments
    /// * `graph`: the graph.
    /// * `output`: the desired output of the algorithm.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: a progress logger.
    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput;
}

/// Computes all the eccentricities of the graph.
///
/// This variant is equivalent to [`AllForward`] in the undirected case.
pub struct All;

impl OutputLevel for All {
    type DirectedOutput = dir_outputs::All;
    type UndirectedOutput = undir_outputs::All;

    fn compute_directed(
        graph: impl RandomAccessGraph + Sync,
        transpose: impl RandomAccessGraph + Sync,
        radial_vertices: Option<AtomicBitVec>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::DirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_directed(
            &graph,
            &transpose,
            Output::All,
            radial_vertices,
            pl,
        );
        computer.compute(thread_pool, pl);

        assert!(
            computer.all_iter.is_some(),
            "Trying to build All without all eccentricities computed"
        );
        assert!(
            computer.forward_iter.is_some(),
            "Trying to build All without all forward eccentricities computed"
        );
        assert!(
            computer.diameter_iterations.is_some(),
            "Trying to build All without the diameter computed"
        );
        assert!(
            computer.radius_iterations.is_some(),
            "Trying to build All without the radius computed"
        );

        let diameter = computer.diameter_low;
        let radius = computer.radius_high;
        let diametral_vertex = computer.diameter_vertex;
        let radial_vertex = computer.radius_vertex;
        let radius_iterations = computer.radius_iterations.unwrap();
        let diameter_iterations = computer.diameter_iterations.unwrap();
        let forward_iterations = computer.forward_iter.unwrap();
        let all_iterations = computer.all_iter.unwrap();
        let forward_eccentricities = computer.forward_low;
        let backward_eccentricities = computer.backward_high;

        Self::DirectedOutput {
            forward_eccentricities,
            backward_eccentricities,
            diameter,
            radius,
            diametral_vertex,
            radial_vertex,
            radius_iterations,
            diameter_iterations,
            forward_iterations,
            all_iterations,
        }
    }

    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_undirected(&graph, Output::All, pl);
        computer.compute(thread_pool, pl);

        assert!(
            computer.forward_iter.is_some(),
            "Trying to build All without all forward eccentricities computed"
        );
        assert!(
            computer.diameter_iterations.is_some(),
            "Trying to build All without the diameter computed"
        );
        assert!(
            computer.radius_iterations.is_some(),
            "Trying to build All without the radius computed"
        );

        let diameter = computer.diameter_low;
        let radius = computer.radius_high;
        let diametral_vertex = computer.diameter_vertex;
        let radial_vertex = computer.radius_vertex;
        let radius_iterations = computer.radius_iterations.unwrap();
        let diameter_iterations = computer.diameter_iterations.unwrap();
        let iterations = computer.forward_iter.unwrap();
        let eccentricities = computer.forward_low;

        Self::UndirectedOutput {
            eccentricities,
            diameter,
            radius,
            diametral_vertex,
            radial_vertex,
            radius_iterations,
            diameter_iterations,
            iterations,
        }
    }
}

/// Computes all the forward eccentricities of the graph.
pub struct AllForward;

impl OutputLevel for AllForward {
    type DirectedOutput = dir_outputs::AllForward;
    type UndirectedOutput = undir_outputs::All;

    fn compute_directed(
        graph: impl RandomAccessGraph + Sync,
        transpose: impl RandomAccessGraph + Sync,
        radial_vertices: Option<AtomicBitVec>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::DirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_directed(
            &graph,
            &transpose,
            Output::AllForward,
            radial_vertices,
            pl,
        );
        computer.compute(thread_pool, pl);

        assert!(
            computer.forward_iter.is_some(),
            "Trying to build AllForward without all forward eccentricities computed"
        );
        assert!(
            computer.diameter_iterations.is_some(),
            "Trying to build AllForward without the diameter computed"
        );
        assert!(
            computer.radius_iterations.is_some(),
            "Trying to build AllForward without the radius computed"
        );

        let diameter = computer.diameter_low;
        let radius = computer.radius_high;
        let diametral_vertex = computer.diameter_vertex;
        let radial_vertex = computer.radius_vertex;
        let radius_iterations = computer.radius_iterations.unwrap();
        let diameter_iterations = computer.diameter_iterations.unwrap();
        let forward_iterations = computer.forward_iter.unwrap();
        let forward_eccentricities = computer.forward_low;

        Self::DirectedOutput {
            forward_eccentricities,
            diameter,
            radius,
            diametral_vertex,
            radial_vertex,
            radius_iterations,
            diameter_iterations,
            forward_iterations,
        }
    }

    #[inline(always)]
    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput {
        All::compute_undirected(graph, thread_pool, pl)
    }
}

/// Computes both the diameter and the radius of the graph.
pub struct RadiusDiameter;

impl OutputLevel for RadiusDiameter {
    type DirectedOutput = dir_outputs::RadiusDiameter;
    type UndirectedOutput = undir_outputs::RadiusDiameter;

    fn compute_directed(
        graph: impl RandomAccessGraph + Sync,
        transpose: impl RandomAccessGraph + Sync,
        radial_vertices: Option<AtomicBitVec>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::DirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_directed(
            &graph,
            &transpose,
            Output::RadiusDiameter,
            radial_vertices,
            pl,
        );
        computer.compute(thread_pool, pl);

        assert!(
            computer.diameter_iterations.is_some(),
            "Trying to build RadiusDiameter without the diameter computed"
        );
        assert!(
            computer.radius_iterations.is_some(),
            "Trying to build RadiusDiameter without the radius computed"
        );

        let diameter = computer.diameter_low;
        let radius = computer.radius_high;
        let diametral_vertex = computer.diameter_vertex;
        let radial_vertex = computer.radius_vertex;
        let radius_iterations = computer.radius_iterations.unwrap();
        let diameter_iterations = computer.diameter_iterations.unwrap();

        Self::DirectedOutput {
            diameter,
            radius,
            diametral_vertex,
            radial_vertex,
            radius_iterations,
            diameter_iterations,
        }
    }

    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput {
        let mut computer =
            DirExactSumSweepComputer::new_undirected(&graph, Output::RadiusDiameter, pl);
        computer.compute(thread_pool, pl);

        assert!(
            computer.diameter_iterations.is_some(),
            "Trying to build RadiusDiameter without the diameter computed"
        );
        assert!(
            computer.radius_iterations.is_some(),
            "Trying to build RadiusDiameter without the radius computed"
        );

        let diameter = computer.diameter_low;
        let radius = computer.radius_high;
        let diametral_vertex = computer.diameter_vertex;
        let radial_vertex = computer.radius_vertex;
        let radius_iterations = computer.radius_iterations.unwrap();
        let diameter_iterations = computer.diameter_iterations.unwrap();

        Self::UndirectedOutput {
            diameter,
            radius,
            diametral_vertex,
            radial_vertex,
            radius_iterations,
            diameter_iterations,
        }
    }
}

/// Computes the diameter of the graph.
pub struct Diameter;

impl OutputLevel for Diameter {
    type DirectedOutput = dir_outputs::Diameter;
    type UndirectedOutput = undir_outputs::Diameter;

    fn compute_directed(
        graph: impl RandomAccessGraph + Sync,
        transpose: impl RandomAccessGraph + Sync,
        radial_vertices: Option<AtomicBitVec>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::DirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_directed(
            &graph,
            &transpose,
            Output::Diameter,
            radial_vertices,
            pl,
        );
        computer.compute(thread_pool, pl);

        assert!(
            computer.diameter_iterations.is_some(),
            "Trying to build Diameter without the diameter computed"
        );

        let diameter = computer.diameter_low;
        let diametral_vertex = computer.diameter_vertex;
        let diameter_iterations = computer.diameter_iterations.unwrap();

        Self::DirectedOutput {
            diameter,
            diametral_vertex,
            diameter_iterations,
        }
    }

    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_undirected(&graph, Output::Diameter, pl);
        computer.compute(thread_pool, pl);

        assert!(
            computer.diameter_iterations.is_some(),
            "Trying to build Diameter without the diameter computed"
        );

        let diameter = computer.diameter_low;
        let diametral_vertex = computer.diameter_vertex;
        let diameter_iterations = computer.diameter_iterations.unwrap();

        Self::UndirectedOutput {
            diameter,
            diametral_vertex,
            diameter_iterations,
        }
    }
}

/// Computes the radius of the graph.
pub struct Radius;

impl OutputLevel for Radius {
    type DirectedOutput = dir_outputs::Radius;
    type UndirectedOutput = undir_outputs::Radius;

    fn compute_directed(
        graph: impl RandomAccessGraph + Sync,
        transpose: impl RandomAccessGraph + Sync,
        radial_vertices: Option<AtomicBitVec>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::DirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_directed(
            &graph,
            &transpose,
            Output::Radius,
            radial_vertices,
            pl,
        );
        computer.compute(thread_pool, pl);

        assert!(
            computer.radius_iterations.is_some(),
            "Trying to build Radius without the radius computed"
        );

        let radius = computer.radius_high;
        let radial_vertex = computer.radius_vertex;
        let radius_iterations = computer.radius_iterations.unwrap();

        Self::DirectedOutput {
            radius,
            radial_vertex,
            radius_iterations,
        }
    }

    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_undirected(&graph, Output::Radius, pl);
        computer.compute(thread_pool, pl);

        assert!(
            computer.radius_iterations.is_some(),
            "Trying to build Radius without the radius computed"
        );

        let radius = computer.radius_high;
        let radial_vertex = computer.radius_vertex;
        let radius_iterations = computer.radius_iterations.unwrap();

        Self::UndirectedOutput {
            radius,
            radial_vertex,
            radius_iterations,
        }
    }
}
