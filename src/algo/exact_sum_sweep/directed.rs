use crate::{
    algo::{
        diameter::{scc_graph::SccGraph, OutputLevel},
        strongly_connected_components::TarjanStronglyConnectedComponents,
        visits::{
            breadth_first::{Event, ParFair},
            FilterArgs, Parallel,
        },
    },
    traits::{SliceInteriorMutability, StronglyConnectedComponents, UnsafeSliceWrite},
    utils::*,
};
use dsi_progress_logger::no_logging;
use dsi_progress_logger::*;
use nonmax::NonMaxUsize;
use rayon::{prelude::*, ThreadPool};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    RwLock,
};
use sux::bits::AtomicBitVec;
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

const VISIT_GRANULARITY: usize = 32;

/// The results of the computation of the [ExactSumSweep](exact_sum_sweep) algorithm on a directed graph.
///
/// Results can be accessed on a common interface with methods [`Self::radius`], [`Self::diameter`],
/// [`Self::radial_vertex`], [`Self::diametral_vertex`], [`Self::eccentricity`] and [`Self::eccentricities`].
///
/// Information on the number of iterations may be retrieved with [`Self::radius_iterations`],
/// [`Self::diameter_iterations`], [`Self::all_forward_iterations`] and [`Self::all_iterations`].
pub enum ExactSumSweep {
    /// See [`OutputLevel::All`].
    All {
        /// The forward eccentricities
        forward_eccentricities: Box<[usize]>,
        /// The backward eccentricities
        backward_eccentricities: Box<[usize]>,
        /// The diameter.
        diameter: usize,
        /// The radius.
        radius: usize,
        /// A vertex whose eccentricity equals the diameter.
        diametral_vertex: usize,
        /// A vertex whose eccentrivity equals the radius.
        radial_vertex: usize,
        /// Number of iterations before the radius was found.
        radius_iterations: usize,
        /// Number of iterations before the diameter was found.
        diameter_iterations: usize,
        /// Number of iterations before all forward eccentricities were found.
        forward_iterations: usize,
        /// Number of iterations before all eccentricities were found.
        all_iterations: usize,
    },
    /// See [`OutputLevel::AllForward`].
    AllForward {
        /// The forward eccentricities
        forward_eccentricities: Box<[usize]>,
        /// The diameter.
        diameter: usize,
        /// The radius.
        radius: usize,
        /// A vertex whose eccentricity equals the diameter.
        diametral_vertex: usize,
        /// A vertex whose eccentrivity equals the radius.
        radial_vertex: usize,
        /// Number of iterations before the radius was found.
        radius_iterations: usize,
        /// Number of iterations before the diameter was found.
        diameter_iterations: usize,
        /// Number of iterations before all forward eccentricities are found.
        forward_iterations: usize,
    },
    /// See [`OutputLevel::RadiusDiameter`].
    RadiusDiameter {
        /// The diameter.
        diameter: usize,
        /// The radius.
        radius: usize,
        /// A vertex whose eccentricity equals the diameter.
        diametral_vertex: usize,
        /// A vertex whose eccentrivity equals the radius.
        radial_vertex: usize,
        /// Number of iterations before the radius was found.
        radius_iterations: usize,
        /// Number of iterations before the diameter was found.
        diameter_iterations: usize,
    },
    /// See [`OutputLevel::Diameter`].
    Diameter {
        /// The diameter.
        diameter: usize,
        /// A vertex whose eccentricity equals the diameter.
        diametral_vertex: usize,
        /// Number of iterations before the diameter was found.
        diameter_iterations: usize,
    },
    /// See [`OutputLevel::Radius`].
    Radius {
        /// The radius.
        radius: usize,
        /// A vertex whose eccentricity equals the radius.
        radial_vertex: usize,
        /// Number of iterations before the radius was found.
        radius_iterations: usize,
    },
}

impl ExactSumSweep {
    /// Build a new instance to compute the *ExactSumSweep* algorithm on directed graphs
    /// and returns the results.
    ///
    /// # Arguments
    /// * `graph`: the direct graph.
    /// * `transpose`: the transpose of `graph`.
    /// * `output`: the desired output of the algorithm.
    /// * `radial_vertices`: an [`AtomicBitVec`] where `v[i]` is true if node `i` is to be considered
    ///    radial vertex. If [`None`] the algorithm will use the biggest connected component.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: a progress logger.
    pub fn compute(
        graph: &(impl RandomAccessGraph + Sync),
        transpose: &(impl RandomAccessGraph + Sync),
        output: OutputLevel,
        radial_vertices: Option<AtomicBitVec>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self {
        let mut computer =
            DirExactSumSweepComputer::new(graph, transpose, output, radial_vertices, pl);
        computer.compute(thread_pool, pl);
        let diameter = computer.diameter();
        let radius = computer.radius();
        let diametral_vertex = computer.diametral_vertex();
        let radial_vertex = computer.radial_vertex();
        let radius_iterations = computer.radius_iterations();
        let diameter_iterations = computer.diameter_iterations();
        let forward_iter = computer.all_forward_iterations();
        let all_iter = computer.all_iterations();

        match output {
            OutputLevel::All => Self::All {
                forward_eccentricities: computer.forward_low.into_boxed_slice(),
                backward_eccentricities: computer.backward_low.into_boxed_slice(),
                diameter: diameter.expect("Diameter should be computed"),
                radius: radius.expect("Radius should be computed"),
                diametral_vertex: diametral_vertex.expect("Diametral vertex should not be None"),
                radial_vertex: radial_vertex.expect("Radial vertex should not be None"),
                radius_iterations: radius_iterations.expect("Radius iteations should not be None"),
                diameter_iterations: diameter_iterations
                    .expect("Diameter iterations should not be None"),
                forward_iterations: forward_iter.expect("Forward iterations should not be None"),
                all_iterations: all_iter.expect("All iterations should not be None"),
            },
            OutputLevel::AllForward => Self::AllForward {
                forward_eccentricities: computer.forward_low.into_boxed_slice(),
                diameter: diameter.expect("Diameter should be computed"),
                radius: radius.expect("Radius should be computed"),
                diametral_vertex: diametral_vertex.expect("Diametral vertex should not be None"),
                radial_vertex: radial_vertex.expect("Radial vertex should not be None"),
                radius_iterations: radius_iterations.expect("Radius iteations should not be None"),
                diameter_iterations: diameter_iterations
                    .expect("Diameter iterations should not be None"),
                forward_iterations: forward_iter.expect("Forward iterations should not be None"),
            },
            OutputLevel::RadiusDiameter => Self::RadiusDiameter {
                diameter: diameter.expect("Diameter should be computed"),
                radius: radius.expect("Radius should be computed"),
                diametral_vertex: diametral_vertex.expect("Diametral vertex should not be None"),
                radial_vertex: radial_vertex.expect("Radial vertex should not be None"),
                radius_iterations: radius_iterations.expect("Radius iteations should not be None"),
                diameter_iterations: diameter_iterations
                    .expect("Diameter iterations should not be None"),
            },
            OutputLevel::Diameter => Self::Diameter {
                diameter: diameter.expect("Diameter should be computed"),
                diametral_vertex: diametral_vertex.expect("Diametral vertex should not be None"),
                diameter_iterations: diameter_iterations
                    .expect("Diameter iterations should not be None"),
            },
            OutputLevel::Radius => Self::Radius {
                radius: radius.expect("Radius should be computed"),
                radial_vertex: radial_vertex.expect("Radial vertex should not be None"),
                radius_iterations: radius_iterations.expect("Radius iteations should not be None"),
            },
        }
    }
}

impl ExactSumSweep {
    /// Returns the radius of the graph if it has been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radius(&self) -> Option<usize> {
        match self {
            Self::All { radius, .. } => Some(*radius),
            Self::AllForward { radius, .. } => Some(*radius),
            Self::RadiusDiameter { radius, .. } => Some(*radius),
            Self::Diameter { .. } => None,
            Self::Radius { radius, .. } => Some(*radius),
        }
    }

    /// Returns the diameter of the graph if is has been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diameter(&self) -> Option<usize> {
        match self {
            Self::All { diameter, .. } => Some(*diameter),
            Self::AllForward { diameter, .. } => Some(*diameter),
            Self::RadiusDiameter { diameter, .. } => Some(*diameter),
            Self::Diameter { diameter, .. } => Some(*diameter),
            Self::Radius { .. } => None,
        }
    }

    /// Returns a radial vertex if it has been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radial_vertex(&self) -> Option<usize> {
        match self {
            Self::All { radial_vertex, .. } => Some(*radial_vertex),
            Self::AllForward { radial_vertex, .. } => Some(*radial_vertex),
            Self::RadiusDiameter { radial_vertex, .. } => Some(*radial_vertex),
            Self::Diameter { .. } => None,
            Self::Radius { radial_vertex, .. } => Some(*radial_vertex),
        }
    }

    /// Returns a diametral vertex if it has been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diametral_vertex(&self) -> Option<usize> {
        match self {
            Self::All {
                diametral_vertex, ..
            } => Some(*diametral_vertex),
            Self::AllForward {
                diametral_vertex, ..
            } => Some(*diametral_vertex),
            Self::RadiusDiameter {
                diametral_vertex, ..
            } => Some(*diametral_vertex),
            Self::Diameter {
                diametral_vertex, ..
            } => Some(*diametral_vertex),
            Self::Radius { .. } => None,
        }
    }

    /// Returns the eccentricity of a vertex if it has been computed, [`None`] otherwise.
    ///
    /// # Arguments
    /// * `vertex`: The vertex.
    /// * `forward`: Whether to return the forward eccentricity (if `true`) or the backward
    ///   eccentricity (if `false`).
    #[inline(always)]
    pub fn eccentricity(&self, vertex: usize, forward: bool) -> Option<usize> {
        if forward {
            match self {
                Self::All {
                    forward_eccentricities,
                    ..
                } => Some(forward_eccentricities[vertex]),
                Self::AllForward {
                    forward_eccentricities,
                    ..
                } => Some(forward_eccentricities[vertex]),
                Self::RadiusDiameter { .. } => None,
                Self::Diameter { .. } => None,
                Self::Radius { .. } => None,
            }
        } else {
            match self {
                Self::All {
                    backward_eccentricities,
                    ..
                } => Some(backward_eccentricities[vertex]),
                Self::AllForward { .. } => None,
                Self::RadiusDiameter { .. } => None,
                Self::Diameter { .. } => None,
                Self::Radius { .. } => None,
            }
        }
    }

    /// Returns the eccentricities if they have been computed, [`None`] otherwise.
    ///
    /// # Arguments
    /// * `forward`: Whether to return the forward eccentricities (if `true`) or the backward
    ///   eccentricities (if `false`).
    pub fn eccentricities(&self, forward: bool) -> Option<&[usize]> {
        if forward {
            match self {
                Self::All {
                    forward_eccentricities,
                    ..
                } => Some(forward_eccentricities),
                Self::AllForward {
                    forward_eccentricities,
                    ..
                } => Some(forward_eccentricities),
                Self::RadiusDiameter { .. } => None,
                Self::Diameter { .. } => None,
                Self::Radius { .. } => None,
            }
        } else {
            match self {
                Self::All {
                    backward_eccentricities,
                    ..
                } => Some(backward_eccentricities),
                Self::AllForward { .. } => None,
                Self::RadiusDiameter { .. } => None,
                Self::Diameter { .. } => None,
                Self::Radius { .. } => None,
            }
        }
    }

    /// Returns the number of iterations needed to compute the radius if it has
    /// been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radius_iterations(&self) -> Option<usize> {
        match self {
            Self::All {
                radius_iterations, ..
            } => Some(*radius_iterations),
            Self::AllForward {
                radius_iterations, ..
            } => Some(*radius_iterations),
            Self::RadiusDiameter {
                radius_iterations, ..
            } => Some(*radius_iterations),
            Self::Diameter { .. } => None,
            Self::Radius {
                radius_iterations, ..
            } => Some(*radius_iterations),
        }
    }

    /// Returns the number of iterations needed to compute the diameter if it has
    /// been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diameter_iterations(&self) -> Option<usize> {
        match self {
            Self::All {
                diameter_iterations,
                ..
            } => Some(*diameter_iterations),
            Self::AllForward {
                diameter_iterations,
                ..
            } => Some(*diameter_iterations),
            Self::RadiusDiameter {
                diameter_iterations,
                ..
            } => Some(*diameter_iterations),
            Self::Diameter {
                diameter_iterations,
                ..
            } => Some(*diameter_iterations),
            Self::Radius { .. } => None,
        }
    }

    /// Returns the number of iterations needed to compute all forward eccentricities
    /// if they have been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn all_forward_iterations(&self) -> Option<usize> {
        match self {
            Self::All {
                forward_iterations: forward_iter,
                ..
            } => Some(*forward_iter),
            Self::AllForward {
                forward_iterations: forward_iter,
                ..
            } => Some(*forward_iter),
            Self::RadiusDiameter { .. } => None,
            Self::Diameter { .. } => None,
            Self::Radius { .. } => None,
        }
    }

    /// Returns the number of iterations needed to compute all eccentricities if they
    /// have been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn all_iterations(&self) -> Option<usize> {
        match self {
            Self::All {
                all_iterations: all_iter,
                ..
            } => Some(*all_iter),
            Self::AllForward { .. } => None,
            Self::RadiusDiameter { .. } => None,
            Self::Diameter { .. } => None,
            Self::Radius { .. } => None,
        }
    }
}

/// The implementation of the *SumSweep* algorithm on directed graphs.
///
/// The algorithm is started by calling [`Self::compute`] with a progress logger
/// if desired.
///
/// Results can be accessed with methods [`Self::radius`], [`Self::diameter`],
/// [`Self::radial_vertex`], [`Self::diametral_vertex`] and [`Self::eccentricity`].
///
/// Information on the number of iterations may be retrieved with [`Self::radius_iterations`],
/// [`Self::diameter_iterations`], [`Self::all_forward_iterations`] and [`Self::all_iterations`].
struct DirExactSumSweepComputer<
    'a,
    G1: RandomAccessGraph + Sync,
    G2: RandomAccessGraph + Sync,
    SCC: StronglyConnectedComponents,
    V1: Parallel<Event> + Sync,
    V2: Parallel<Event> + Sync,
> {
    graph: &'a G1,
    transpose: &'a G2,
    num_nodes: usize,
    output: OutputLevel,
    radial_vertices: AtomicBitVec,
    /// The lower bound of the diameter.
    diameter_low: usize,
    /// The upper bound of the radius.
    radius_high: usize,
    /// A vertex whose eccentricity equals the diameter.
    diameter_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    radius_vertex: usize,
    /// Number of iterations performed until now.
    iterations: usize,
    /// The lower bound of the forward eccentricities.
    forward_low: Vec<usize>,
    /// The upper boung of the forward eccentricities.
    forward_high: Vec<usize>,
    /// The lower bound of the backward eccentricities.
    backward_low: Vec<usize>,
    /// The upper bound of the backward eccentricities.
    backward_high: Vec<usize>,
    /// Number of iterations before the radius was found.
    radius_iterations: Option<NonMaxUsize>,
    /// Number of iterations before the diameter was found.
    diameter_iterations: Option<NonMaxUsize>,
    /// Number of iterations before all forward eccentricities are found.
    forward_iter: Option<NonMaxUsize>,
    /// Number of iterations before all eccentricities are found.
    all_iter: Option<NonMaxUsize>,
    /// The strongly connected components.
    scc: SCC,
    /// The strongly connected components diagram.
    scc_graph: SccGraph<G1, G2, SCC>,
    /// Total forward distance from already processed vertices (used as tie-break for the choice
    /// of the next vertex to process).
    forward_tot: Vec<usize>,
    /// Total backward distance from already processed vertices (used as tie-break for the choice
    /// of the next vertex to process).
    backward_tot: Vec<usize>,
    compute_radial_vertices: bool,
    visit: V1,
    transposed_visit: V2,
}

impl<'a, G1: RandomAccessGraph + Sync, G2: RandomAccessGraph + Sync>
    DirExactSumSweepComputer<
        'a,
        G1,
        G2,
        TarjanStronglyConnectedComponents,
        ParFair<&'a G1>,
        ParFair<&'a G2>,
    >
{
    /// Build a new instance to compute the *ExactSumSweep* algorithm on directed graphs.
    ///
    /// # Arguments
    /// * `graph`: the direct graph.
    /// * `transpose`: the transpose of `graph`.
    /// * `output`: the desired output of the algorithm.
    /// * `radial_vertices`: an [`AtomicBitVec`] where `v[i]` is true if node `i` is to be considered
    ///    radial vertex. If [`None`] the algorithm will use the biggest connected component.
    /// * `pl`: a progress logger.
    pub fn new(
        graph: &'a G1,
        transpose: &'a G2,
        output: OutputLevel,
        radial_vertices: Option<AtomicBitVec>,
        pl: &mut impl ProgressLog,
    ) -> Self {
        let num_nodes = graph.num_nodes();
        assert!(
            num_nodes < usize::MAX,
            "Graph should have a number of nodes < usize::MAX"
        );

        let scc = TarjanStronglyConnectedComponents::compute(graph, pl);

        let compute_radial_vertices = radial_vertices.is_none();
        let acc_radial = if let Some(r) = radial_vertices {
            debug_assert_eq!(r.len(), num_nodes);
            r
        } else {
            AtomicBitVec::new(num_nodes)
        };

        let scc_graph = SccGraph::new(graph, transpose, &scc, pl);

        debug_assert_eq!(graph.num_nodes(), transpose.num_nodes());
        debug_assert_eq!(graph.num_arcs(), transpose.num_arcs());
        debug_assert!(
            check_transposed(&graph, &transpose),
            "transpose should be the transpose of graph"
        );

        pl.info(format_args!("Initializing data structure"));

        let lower_forward = vec![0; num_nodes];
        let lower_backward = vec![0; num_nodes];
        let upper_forward = vec![num_nodes + 1; num_nodes];
        let upper_backward = vec![num_nodes + 1; num_nodes];
        let total_forward = vec![0; num_nodes];
        let total_backward = vec![0; num_nodes];

        DirExactSumSweepComputer {
            graph,
            transpose,
            num_nodes,
            forward_tot: total_forward,
            backward_tot: total_backward,
            forward_low: lower_forward,
            forward_high: upper_forward,
            backward_low: lower_backward,
            backward_high: upper_backward,
            scc_graph,
            scc,
            diameter_low: 0,
            radius_high: usize::MAX,
            output,
            radius_iterations: None,
            diameter_iterations: None,
            all_iter: None,
            forward_iter: None,
            iterations: 0,
            radial_vertices: acc_radial,
            radius_vertex: 0,
            diameter_vertex: 0,
            compute_radial_vertices,
            visit: ParFair::new(graph, VISIT_GRANULARITY),
            transposed_visit: ParFair::new(transpose, VISIT_GRANULARITY),
        }
    }
}

impl<
        'a,
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        C: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        V2: Parallel<Event> + Sync,
    > DirExactSumSweepComputer<'a, G1, G2, C, V1, V2>
{
    #[inline(always)]
    fn incomplete_forward(&self, index: usize) -> bool {
        self.forward_low[index] != self.forward_high[index]
    }

    #[inline(always)]
    fn incomplete_backward(&self, index: usize) -> bool {
        self.backward_low[index] != self.backward_high[index]
    }

    /// Performs `iterations` steps of the SumSweep heuristic, starting from vertex `start`.
    ///
    /// # Arguments
    /// * `start`: The starting vertex.
    /// * `iterations`: The number of iterations.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    fn sum_sweep_heuristic(
        &mut self,
        start: usize,
        iterations: usize,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) {
        pl.info(format_args!(
            "Performing initial SumSweep visit from {}.",
            start
        ));
        self.step_sum_sweep(Some(start), true, thread_pool, pl);

        for i in 2..=iterations {
            if i % 2 == 0 {
                let v = math::filtered_argmax(&self.backward_tot, &self.backward_low, |i, _| {
                    self.incomplete_backward(i)
                });
                pl.info(format_args!(
                    "Performing backwards SumSweep visit from {:?}",
                    v
                ));
                self.step_sum_sweep(v, false, thread_pool, pl);
            } else {
                let v = math::filtered_argmax(&self.forward_tot, &self.forward_low, |i, _| {
                    self.incomplete_forward(i)
                });
                pl.info(format_args!(
                    "Performing forward SumSweep visit from {:?}.",
                    v
                ));
                self.step_sum_sweep(v, true, thread_pool, pl);
            }
        }
    }

    /// Computes diameter, radius, and/or all eccentricities.
    ///
    /// Results can be accessed by methods [`Self::radius`], [`Self::diameter`], [`Self::radial_vertex`],
    /// [`Self::diametral_vertex`], [`Self::eccentricity`].
    ///
    /// # Arguments
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    pub fn compute(&mut self, thread_pool: &ThreadPool, pl: &mut impl ProgressLog) {
        if self.num_nodes == 0 {
            return;
        }

        pl.start("Computing SumSweep...");

        if self.compute_radial_vertices {
            self.compute_radial_vertices(thread_pool, &mut pl.clone());
        }

        let max_outdegree_vertex = thread_pool
            .install(|| {
                (0..self.num_nodes)
                    .into_par_iter()
                    .map(|v| (self.graph.outdegree(v), v))
                    .max_by_key(|x| x.0)
            })
            .unwrap()
            .1; // The iterator is not empty

        self.sum_sweep_heuristic(max_outdegree_vertex, 6, thread_pool, &mut pl.clone());

        let mut points = [self.graph.num_nodes() as f64; 5];
        let mut missing_nodes = self.find_missing_nodes(thread_pool, &mut pl.clone());
        let mut old_missing_nodes;

        pl.info(format_args!(
            "Missing nodes: {} out of {}",
            missing_nodes,
            self.num_nodes * 2
        ));

        while missing_nodes > 0 {
            let step_to_perform = math::argmax(&points).expect("Could not find step to perform");

            match step_to_perform {
                0 => {
                    pl.info(format_args!("Performing all_cc_upper_bound."));
                    let pivot = self.find_best_pivot(&mut pl.clone());
                    self.all_cc_upper_bound(pivot, thread_pool, &mut pl.clone())
                }
                1 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex maximizing the upper bound."
                    ));
                    let v = math::filtered_argmax(&self.forward_high, &self.forward_tot, |i, _| {
                        self.incomplete_forward(i)
                    });
                    self.step_sum_sweep(v, true, thread_pool, &mut pl.clone())
                }
                2 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex minimizing the lower bound."
                    ));
                    let v = math::filtered_argmin(&self.forward_low, &self.forward_tot, |i, _| {
                        self.radial_vertices[i]
                    });
                    self.step_sum_sweep(v, true, thread_pool, &mut pl.clone())
                }
                3 => {
                    pl.info(format_args!(
                        "Performing a backward BFS from a vertex maximizing the upper bound."
                    ));
                    let v =
                        math::filtered_argmax(&self.backward_high, &self.backward_tot, |i, _| {
                            self.incomplete_backward(i)
                        });
                    self.step_sum_sweep(v, false, thread_pool, &mut pl.clone())
                }
                4 => {
                    pl.info(format_args!(
                        "Performing a backward BFS, from a vertex maximizing the distance sum."
                    ));
                    let v =
                        math::filtered_argmax(&self.backward_tot, &self.backward_high, |i, _| {
                            self.incomplete_backward(i)
                        });
                    self.step_sum_sweep(v, false, thread_pool, &mut pl.clone())
                }
                5.. => panic!(),
            }

            old_missing_nodes = missing_nodes;
            missing_nodes = self.find_missing_nodes(thread_pool, &mut pl.clone());
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
                self.num_nodes * 2
            ));
        }

        if self.output == OutputLevel::Radius || self.output == OutputLevel::RadiusDiameter {
            pl.info(format_args!(
                "Radius: {} ({} iterations).",
                self.radius_high,
                self.radius_iterations
                    .expect("radius iterations should not be None")
            ));
        }
        if self.output == OutputLevel::Diameter || self.output == OutputLevel::RadiusDiameter {
            pl.info(format_args!(
                "Diameter: {} ({} iterations).",
                self.diameter_low,
                self.diameter_iterations
                    .expect("radius iterations should not be None"),
            ));
        }
        pl.done();
    }

    /// Returns the radius of the graph if it has already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radius(&self) -> Option<usize> {
        self.radius_iterations.map(|_| self.radius_high)
    }

    /// Returns the diameter of the graph if is has already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diameter(&self) -> Option<usize> {
        self.diameter_iterations.map(|_| self.diameter_low)
    }

    /// Returns a radial vertex if it has already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radial_vertex(&self) -> Option<usize> {
        self.radius_iterations.map(|_| self.radius_vertex)
    }

    /// Returns a diametral vertex if it has already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diametral_vertex(&self) -> Option<usize> {
        self.diameter_iterations.map(|_| self.diameter_vertex)
    }

    /// Returns the number of iterations needed to compute the radius if it has already
    /// been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radius_iterations(&self) -> Option<usize> {
        self.radius_iterations.map(|v| v.into())
    }

    /// Returns the number of iterations needed to compute the diameter if it has already
    /// been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn diameter_iterations(&self) -> Option<usize> {
        self.diameter_iterations.map(|v| v.into())
    }

    /// Returns the number of iterations needed to compute all forward eccentricities
    /// if they have already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn all_forward_iterations(&self) -> Option<usize> {
        self.forward_iter.map(|v| v.into())
    }

    /// Returns the number of iterations needed to compute all eccentricities if they
    /// have already been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn all_iterations(&self) -> Option<usize> {
        self.all_iter.map(|v| v.into())
    }

    /// Uses a heuristic to decide which is the best pivot to choose in each strongly connected
    /// component, in order to perform the [`Self::all_cc_upper_bound`] method.
    ///
    /// # Arguments
    /// * `pl`: A progress logger..
    fn find_best_pivot(&self, pl: &mut impl ProgressLog) -> Vec<usize> {
        debug_assert!(self.num_nodes < usize::MAX);

        let mut pivot: Vec<Option<NonMaxUsize>> = vec![None; self.scc.number_of_components()];
        let components = self.scc.component();
        pl.expected_updates(Some(components.len()));
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.start("Computing best pivot");

        for (v, &component) in components.iter().enumerate().rev() {
            if let Some(p) = pivot[component] {
                let p = p.into();
                let current = self.backward_low[v]
                    + self.forward_low[v]
                    + if self.incomplete_forward(v) {
                        0
                    } else {
                        self.num_nodes
                    }
                    + if self.incomplete_backward(v) {
                        0
                    } else {
                        self.num_nodes
                    };

                let best = self.backward_low[p]
                    + self.forward_low[p]
                    + if self.incomplete_forward(p) {
                        0
                    } else {
                        self.num_nodes
                    }
                    + if self.incomplete_backward(p) {
                        0
                    } else {
                        self.num_nodes
                    };

                if current < best
                    || (current == best
                        && self.forward_tot[v] + self.backward_tot[v]
                            <= self.forward_tot[p] + self.backward_tot[p])
                {
                    pivot[component] = NonMaxUsize::new(v);
                }
            } else {
                pivot[component] = NonMaxUsize::new(v);
            }
            pl.light_update();
        }

        pl.done();

        pivot.into_iter().map(|x| x.unwrap().into()).collect()
    }

    /// Computes and stores in variable [`Self::radial_vertices`] the set of vertices that are
    /// either in the biggest strongly connected component or that are able to reach vertices in
    /// the biggest strongly connected component.
    ///
    /// # Arguments
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    fn compute_radial_vertices(&mut self, thread_pool: &ThreadPool, pl: &mut impl ProgressLog) {
        if self.num_nodes == 0 {
            return;
        }

        pl.expected_updates(None);
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.start("Computing radial vertices...");

        let component = self.scc.component();
        let scc_sizes = self.scc.compute_sizes();
        let max_size_scc = math::argmax(&scc_sizes).expect("Could not find max size scc.");

        pl.info(format_args!(
            "Searching for biggest strongly connected component"
        ));

        let mut v = self.num_nodes;

        while v > 0 {
            v -= 1;
            if component[v] == max_size_scc {
                break;
            }
        }

        pl.info(format_args!("Computing radial vertices set"));

        let radial_vertices = &self.radial_vertices;
        self.transposed_visit
            .visit(
                v,
                |event| {
                    if let Event::Unknown { curr, .. } = event {
                        radial_vertices.set(curr, true, Ordering::Relaxed)
                    }
                    Ok(())
                },
                thread_pool,
                pl,
            )
            .unwrap_infallible();
        self.transposed_visit.reset();

        pl.done();
    }

    /// Performs a (forward or backward) BFS, updating lower bounds on the eccentricities
    /// of all visited vertices.
    ///
    /// # Arguments
    /// * `start`: The starting vertex of the BFS. If [`None`], no visit happens.
    /// * `forward`: Whether the BFS is performed following the direction of edges or
    ///   in the opposite direction.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    fn step_sum_sweep(
        &mut self,
        start: Option<usize>,
        forward: bool,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) {
        if let Some(start) = start {
            if forward {
                self.forward_step_sum_sweep(start, thread_pool, pl);
            } else {
                self.backwards_step_sum_sweep(start, thread_pool, pl);
            }
            self.iterations += 1;
        }
    }

    #[inline(always)]
    fn backwards_step_sum_sweep(
        &mut self,
        start: usize,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) {
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.expected_updates(None);
        pl.start(format!("Performing backwards BFS starting from {}", start));

        let max_dist = AtomicUsize::new(0);
        let radius = RwLock::new((self.radius_high, self.radius_vertex));

        let forward_low = self.forward_low.as_mut_slice_of_cells();
        let forward_tot = self.forward_tot.as_mut_slice_of_cells();

        self.transposed_visit
            .visit(
                start,
                |event| {
                    if let Event::Unknown {
                        curr: node,
                        distance,
                        ..
                    } = event
                    {
                        // Safety for unsafe blocks: each node gets accessed exactly once, so no data races can happen
                        max_dist.fetch_max(distance, Ordering::Relaxed);

                        let node_forward_low_ptr = unsafe { forward_low.get_mut_unsafe(node) };
                        let node_forward_tot_ptr = unsafe { forward_tot.get_mut_unsafe(node) };

                        let node_forward_low = unsafe { *node_forward_low_ptr };
                        let node_forward_high = self.forward_high[node];

                        unsafe {
                            *node_forward_tot_ptr += distance;
                        }
                        if node_forward_low != node_forward_high && node_forward_low < distance {
                            unsafe {
                                *node_forward_low_ptr = distance;
                            }

                            if distance == node_forward_high && self.radial_vertices[node] {
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
                    };
                    Ok(())
                },
                thread_pool,
                pl,
            )
            .unwrap_infallible();

        self.transposed_visit.reset();

        let ecc_start = max_dist.load(Ordering::Relaxed);

        self.backward_low[start] = ecc_start;
        self.backward_high[start] = ecc_start;

        (self.radius_high, self.radius_vertex) = radius.into_inner().unwrap();

        if self.diameter_low < ecc_start {
            self.diameter_low = ecc_start;
            self.diameter_vertex = start;
        }

        pl.done();
    }

    #[inline(always)]
    fn forward_step_sum_sweep(
        &mut self,
        start: usize,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) {
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.expected_updates(None);
        pl.start(format!("Performing forward BFS starting from {}", start));

        let max_dist = AtomicUsize::new(0);

        let backward_low = self.backward_low.as_mut_slice_of_cells();
        let backward_tot = self.backward_tot.as_mut_slice_of_cells();

        self.visit
            .visit(
                start,
                |event| {
                    if let Event::Unknown {
                        curr: node,
                        distance,
                        ..
                    } = event
                    {
                        // Safety for unsafe blocks: each node gets accessed exactly once, so no data races can happen
                        max_dist.fetch_max(distance, Ordering::Relaxed);

                        let node_backward_low_ptr = unsafe { backward_low.get_mut_unsafe(node) };
                        let node_backward_tot_ptr = unsafe { backward_tot.get_mut_unsafe(node) };

                        let node_backward_low = unsafe { *node_backward_low_ptr };
                        let node_backward_high = self.backward_high[node];

                        unsafe {
                            *node_backward_tot_ptr += distance;
                        }
                        if node_backward_low != node_backward_high && node_backward_low < distance {
                            unsafe {
                                *node_backward_low_ptr = distance;
                            }
                        }
                    }
                    Ok(())
                },
                thread_pool,
                pl,
            )
            .unwrap_infallible();
        self.visit.reset();

        let ecc_start = max_dist.load(Ordering::Relaxed);

        self.forward_low[start] = ecc_start;
        self.forward_high[start] = ecc_start;

        if self.diameter_low < ecc_start {
            self.diameter_low = ecc_start;
            self.diameter_vertex = start;
        }
        if self.radial_vertices[start] && self.radius_high > ecc_start {
            self.radius_high = ecc_start;
            self.radius_vertex = start;
        }

        pl.done();
    }

    /// Performs a (forward or backward) BFS inside each strongly connected component, starting
    /// from the pivot.
    ///
    /// # Arguments
    /// * `pivot`: An array containing in position `i` the pivot of the `i`-th strongly connected
    ///   component.
    /// * `forward`: Whether the BFS is performed following the direction of edges or
    ///   in the opposite direction.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
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
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> (Vec<usize>, Vec<usize>) {
        pl.expected_updates(None);
        pl.display_memory(false);

        let (dist_pivot, usize_ecc_pivot) = if forward {
            pl.start("Computing forward dist pivots");
            self.compute_dist_pivot_from_graph(pivot, self.graph, thread_pool)
        } else {
            pl.start("Computing backwards dist pivots");
            self.compute_dist_pivot_from_graph(pivot, self.transpose, thread_pool)
        };

        pl.done();

        (dist_pivot, usize_ecc_pivot)
    }

    #[inline(always)]
    fn compute_dist_pivot_from_graph(
        &self,
        pivot: &[usize],
        graph: &(impl RandomAccessGraph + Sync),
        thread_pool: &ThreadPool,
    ) -> (Vec<usize>, Vec<usize>) {
        let components = self.scc.component();
        let ecc_pivot = closure_vec(|| AtomicUsize::new(0), self.scc.number_of_components());
        let mut dist_pivot = vec![0; self.num_nodes];
        let dist_pivot_mut = dist_pivot.as_mut_slice_of_cells();
        let current_index = AtomicUsize::new(0);

        thread_pool.broadcast(|_| {
            let mut bfs = ParFair::new(graph, VISIT_GRANULARITY);
            let mut current_pivot_index = current_index.fetch_add(1, Ordering::Relaxed);

            while let Some(&p) = pivot.get(current_pivot_index) {
                let pivot_component = components[p];
                let component_ecc_pivot = &ecc_pivot[pivot_component];

                bfs.visit_filtered(
                    p,
                    |event| {
                        if let Event::Unknown { curr, distance, .. } = event {
                            // Safety: each node is accessed exactly once
                            unsafe {
                                dist_pivot_mut.write_once(curr, distance);
                            }
                            component_ecc_pivot.store(distance, Ordering::Relaxed);
                        };
                        Ok(())
                    },
                    |FilterArgs::<Event> { curr, .. }| components[curr] == pivot_component,
                    thread_pool,
                    no_logging![],
                )
                .unwrap_infallible();

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

        (dist_pivot, usize_ecc_pivot)
    }

    /// Performs a step of the ExactSumSweep algorithm.
    ///
    /// # Arguments
    /// * `pivot`: An array containing in position `i` the pivot of the `i`-th strongly connected component.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    fn all_cc_upper_bound(
        &mut self,
        pivot: Vec<usize>,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) {
        pl.item_name("elements");
        pl.display_memory(false);
        pl.expected_updates(Some(
            pivot.len() + self.scc.number_of_components() + self.num_nodes,
        ));
        pl.start("Performing AllCCUpperBound step of ExactSumSweep algorithm");

        let (dist_pivot_f, mut ecc_pivot_f) =
            self.compute_dist_pivot(&pivot, true, thread_pool, &mut pl.clone());
        let (dist_pivot_b, mut ecc_pivot_b) =
            self.compute_dist_pivot(&pivot, false, thread_pool, &mut pl.clone());
        let components = self.scc.component();

        // Tarjan's algorithm emits components in reverse topological order.
        // In order to bound forward eccentricities in reverse topological order the components
        // are traversed as is.
        for (c, &p) in pivot.iter().enumerate() {
            for connection in self.scc_graph.children(c) {
                let next_c = connection.target;
                let start = connection.start;
                let end = connection.end;

                ecc_pivot_f[c] = std::cmp::max(
                    ecc_pivot_f[c],
                    dist_pivot_f[start] + 1 + dist_pivot_b[end] + ecc_pivot_f[next_c],
                );

                if ecc_pivot_f[c] >= self.forward_high[p] {
                    ecc_pivot_f[c] = self.forward_high[p];
                    break;
                }
            }
            pl.light_update();
        }

        // Tarjan's algorithm emits components in reverse topological order.
        // In order to bound backward eccentricities in topological order the components order
        // must be reversed.
        for c in (0..self.scc.number_of_components()).rev() {
            for component in self.scc_graph.children(c) {
                let next_c = component.target;
                let start = component.start;
                let end = component.end;

                ecc_pivot_b[next_c] = std::cmp::max(
                    ecc_pivot_b[next_c],
                    dist_pivot_f[start] + 1 + dist_pivot_b[end] + ecc_pivot_b[c],
                );

                if ecc_pivot_b[next_c] >= self.backward_high[pivot[next_c]] {
                    ecc_pivot_b[next_c] = self.backward_high[pivot[next_c]];
                }
            }
            pl.light_update();
        }

        let radius = RwLock::new((self.radius_high, self.radius_vertex));

        let forward_high = self.forward_high.as_mut_slice_of_cells();
        let backward_high = self.backward_high.as_mut_slice_of_cells();

        thread_pool.install(|| {
            (0..self.num_nodes).into_par_iter().for_each(|node| {
                // Safety for unsafe blocks: each node gets accessed exactly once, so no data races can happen
                unsafe {
                    forward_high.write_once(
                        node,
                        std::cmp::min(
                            forward_high[node].read(),
                            dist_pivot_b[node] + ecc_pivot_f[components[node]],
                        ),
                    );
                }

                if forward_high[node].read() == self.forward_low[node] {
                    let new_ecc = forward_high[node].read();

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
                    backward_high.write_once(
                        node,
                        std::cmp::min(
                            backward_high[node].read(),
                            dist_pivot_f[node] + ecc_pivot_b[components[node]],
                        ),
                    );
                }
            });
        });

        pl.update_with_count(self.num_nodes);

        (self.radius_high, self.radius_vertex) = radius.into_inner().unwrap();

        self.iterations += 3;

        pl.done();
    }

    /// Computes how many nodes are still to be processed, before outputting the result.
    ///
    /// # Arguments
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: A progress logger.
    fn find_missing_nodes(&mut self, thread_pool: &ThreadPool, pl: &mut impl ProgressLog) -> usize {
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.expected_updates(Some(self.num_nodes));
        pl.start("Computing missing nodes");

        let (missing_r, missing_df, missing_db, missing_all_forward, missing_all_backward) =
            thread_pool.install(|| {
                (0..self.num_nodes)
                    .into_par_iter()
                    .fold(
                        || (0, 0, 0, 0, 0),
                        |mut acc, node| {
                            if self.incomplete_forward(node) {
                                acc.3 += 1;
                                if self.forward_high[node] > self.diameter_low {
                                    acc.1 += 1;
                                }
                                if self.radial_vertices[node]
                                    && self.forward_low[node] < self.radius_high
                                {
                                    acc.0 += 1;
                                }
                            }
                            if self.incomplete_backward(node) {
                                acc.4 += 1;
                                if self.backward_high[node] > self.diameter_low {
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

        pl.update_with_count(self.num_nodes);

        let iterations =
            NonMaxUsize::new(self.iterations).expect("Iterations should never be usize::MAX");

        if missing_r == 0 && self.radius_iterations.is_none() {
            self.radius_iterations = Some(iterations);
        }
        if (missing_df == 0 || missing_db == 0) && self.diameter_iterations.is_none() {
            self.diameter_iterations = Some(iterations);
        }
        if missing_all_forward == 0 && self.forward_iter.is_none() {
            self.forward_iter = Some(iterations);
        }
        if missing_all_forward == 0 && missing_all_backward == 0 {
            self.all_iter = Some(iterations);
        }

        pl.done();

        match self.output {
            OutputLevel::Radius => missing_r,
            OutputLevel::Diameter => std::cmp::min(missing_df, missing_db),
            OutputLevel::RadiusDiameter => missing_r + std::cmp::min(missing_df, missing_db),
            OutputLevel::AllForward => missing_all_forward,
            OutputLevel::All => missing_all_backward + missing_all_forward,
        }
    }
}
