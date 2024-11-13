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
        let mut computer =
            DirExactSumSweepComputer::new(&graph, &transpose, Output::All, radial_vertices, pl);
        computer.compute(thread_pool, pl);

        Self::DirectedOutput {
            // TODO
            forward_eccentricities: std::mem::take(&mut computer.forward_low).into_boxed_slice(),
            backward_eccentricities: std::mem::take(&mut computer.backward_low).into_boxed_slice(),
            diameter: computer.diameter().unwrap(),
            radius: computer.radius().unwrap(),
            diametral_vertex: computer.diametral_vertex().unwrap(),
            radial_vertex: computer.radial_vertex().unwrap(),
            radius_iterations: computer.radius_iterations().unwrap(),
            diameter_iterations: computer.diameter_iterations().unwrap(),
            forward_iterations: computer.all_forward_iterations().unwrap(),
            all_iterations: computer.all_iterations().unwrap(),
        }
    }

    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_undirected(&graph, Output::All, pl);
        computer.compute(thread_pool, pl);

        Self::UndirectedOutput {
            eccentricities: std::mem::take(&mut computer.forward_low).into_boxed_slice(),
            diameter: computer.diameter().unwrap(),
            radius: computer.radius().unwrap(),
            diametral_vertex: computer.diametral_vertex().unwrap(),
            radial_vertex: computer.radial_vertex().unwrap(),
            radius_iterations: computer.radius_iterations().unwrap(),
            diameter_iterations: computer.diameter_iterations().unwrap(),
            iterations: computer.all_forward_iterations().unwrap(),
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
        let mut computer = DirExactSumSweepComputer::new(
            &graph,
            &transpose,
            Output::AllForward,
            radial_vertices,
            pl,
        );
        computer.compute(thread_pool, pl);

        Self::DirectedOutput {
            forward_eccentricities: std::mem::take(&mut computer.forward_low).into_boxed_slice(),
            diameter: computer.diameter().unwrap(),
            radius: computer.radius().unwrap(),
            diametral_vertex: computer.diametral_vertex().unwrap(),
            radial_vertex: computer.radial_vertex().unwrap(),
            radius_iterations: computer.radius_iterations().unwrap(),
            diameter_iterations: computer.diameter_iterations().unwrap(),
            forward_iterations: computer.all_forward_iterations().unwrap(),
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
        let mut computer = DirExactSumSweepComputer::new(
            &graph,
            &transpose,
            Output::RadiusDiameter,
            radial_vertices,
            pl,
        );
        computer.compute(thread_pool, pl);

        Self::DirectedOutput {
            diameter: computer.diameter().unwrap(),
            radius: computer.radius().unwrap(),
            diametral_vertex: computer.diametral_vertex().unwrap(),
            radial_vertex: computer.radial_vertex().unwrap(),
            radius_iterations: computer.radius_iterations().unwrap(),
            diameter_iterations: computer.diameter_iterations().unwrap(),
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

        Self::UndirectedOutput {
            diameter: computer.diameter().unwrap(),
            radius: computer.radius().unwrap(),
            diametral_vertex: computer.diametral_vertex().unwrap(),
            radial_vertex: computer.radial_vertex().unwrap(),
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
        let mut computer = DirExactSumSweepComputer::new(
            &graph,
            &transpose,
            Output::Diameter,
            radial_vertices,
            pl,
        );
        computer.compute(thread_pool, pl);

        Self::DirectedOutput {
            diameter: computer.diameter().unwrap(),
            diametral_vertex: computer.diametral_vertex().unwrap(),
            diameter_iterations: computer.diameter_iterations().unwrap(),
        }
    }

    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_undirected(&graph, Output::Diameter, pl);
        computer.compute(thread_pool, pl);

        Self::UndirectedOutput {
            diameter: computer.diameter().unwrap(),
            diametral_vertex: computer.diametral_vertex().unwrap(),
            diameter_iterations: computer.diameter_iterations().unwrap(),
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
        let mut computer =
            DirExactSumSweepComputer::new(&graph, &transpose, Output::Radius, radial_vertices, pl);
        computer.compute(thread_pool, pl);

        Self::DirectedOutput {
            radius: computer.radius().unwrap(),
            radial_vertex: computer.radial_vertex().unwrap(),
            radius_iterations: computer.radius_iterations().unwrap(),
        }
    }

    fn compute_undirected(
        graph: impl RandomAccessGraph + Sync,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self::UndirectedOutput {
        let mut computer = DirExactSumSweepComputer::new_undirected(&graph, Output::Radius, pl);
        computer.compute(thread_pool, pl);

        Self::UndirectedOutput {
            radius: computer.radius().unwrap(),
            radial_vertex: computer.radial_vertex().unwrap(),
            radius_iterations: computer.radius_iterations().unwrap(),
        }
    }
}
