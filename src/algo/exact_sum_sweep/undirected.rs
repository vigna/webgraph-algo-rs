use crate::{algo::diameter::*, utils::check_symmetric};
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
pub enum UndirExactSumSweep {
    /// See [`OutputLevel::All`].
    All {
        /// The eccentricities
        eccentricities: Box<[usize]>,
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
        /// Number of iterations before all eccentricities were found.
        iterations: usize,
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
        /// The radius.
        /// A vertex whose eccentricity equals the diameter.
        diametral_vertex: usize,
        /// Number of iterations before the diameter was found.
        diameter_iterations: usize,
    },
    /// See [`OutputLevel::Radius`].
    Radius {
        /// The radius.
        radius: usize,
        /// A vertex whose eccentrivity equals the radius.
        radial_vertex: usize,
        /// Number of iterations before the radius was found.
        radius_iterations: usize,
    },
}

impl From<ExactSumSweep> for UndirExactSumSweep {
    fn from(sum_sweep: ExactSumSweep) -> Self {
        match sum_sweep {
            ExactSumSweep::AllForward {
                forward_eccentricities,
                diameter,
                radius,
                diametral_vertex,
                radial_vertex,
                radius_iterations,
                diameter_iterations,
                forward_iterations,
            } => Self::All {
                eccentricities: forward_eccentricities,
                diameter,
                radius,
                diametral_vertex,
                radial_vertex,
                radius_iterations,
                diameter_iterations,
                iterations: forward_iterations,
            },
            ExactSumSweep::RadiusDiameter {
                diameter,
                radius,
                diametral_vertex,
                radial_vertex,
                radius_iterations,
                diameter_iterations,
            } => Self::RadiusDiameter {
                diameter,
                radius,
                diametral_vertex,
                radial_vertex,
                radius_iterations,
                diameter_iterations,
            },
            ExactSumSweep::Diameter {
                diameter,
                diametral_vertex,
                diameter_iterations,
            } => Self::Diameter {
                diameter,
                diametral_vertex,
                diameter_iterations,
            },
            ExactSumSweep::Radius {
                radius,
                radial_vertex,
                radius_iterations,
            } => Self::Radius {
                radius,
                radial_vertex,
                radius_iterations,
            },
            _ => {
                unreachable!("The undirected version of the algorithm does not support this output")
            }
        }
    }
}

impl UndirExactSumSweep {
    /// Build a new instance to compute the *ExactSumSweep* algorithm on undirected graphs
    /// and returns the results.
    ///
    /// # Arguments
    /// * `graph`: the direct graph.
    /// * `output`: the desired output of the algorithm.
    /// * `thread_pool`: The thread pool to use for parallel computation.
    /// * `pl`: a progress logger.
    pub fn compute(
        graph: impl RandomAccessGraph + Sync,
        output: OutputLevel,
        thread_pool: &ThreadPool,
        pl: &mut impl ProgressLog,
    ) -> Self {
        debug_assert!(check_symmetric(&graph), "graph should be symmetric");
        // All and AllForward are equivalent for undirected graphs
        let output = match output {
            OutputLevel::Radius => OutputLevel::Radius,
            OutputLevel::Diameter => OutputLevel::Diameter,
            OutputLevel::RadiusDiameter => OutputLevel::RadiusDiameter,
            _ => OutputLevel::AllForward,
        };
        ExactSumSweep::compute(&graph, &graph, output, None, thread_pool, pl).into()
    }
}

impl UndirExactSumSweep {
    /// Returns the radius of the graph if it has been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn radius(&self) -> Option<usize> {
        match self {
            Self::All { radius, .. } => Some(*radius),
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
    #[inline(always)]
    pub fn eccentricity(&self, vertex: usize) -> Option<usize> {
        match self {
            Self::All { eccentricities, .. } => Some(eccentricities[vertex]),
            Self::RadiusDiameter { .. } => None,
            Self::Diameter { .. } => None,
            Self::Radius { .. } => None,
        }
    }

    /// Returns the eccentricities if they have been computed, [`None`] otherwise.
    pub fn eccentricities(&self) -> Option<&[usize]> {
        match self {
            Self::All { eccentricities, .. } => Some(eccentricities),
            Self::RadiusDiameter { .. } => None,
            Self::Diameter { .. } => None,
            Self::Radius { .. } => None,
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

    /// Returns the number of iterations needed to compute all eccentricities if they
    /// have been computed, [`None`] otherwise.
    #[inline(always)]
    pub fn all_iterations(&self) -> Option<usize> {
        match self {
            Self::All {
                iterations: iters, ..
            } => Some(*iters),
            Self::RadiusDiameter { .. } => None,
            Self::Diameter { .. } => None,
            Self::Radius { .. } => None,
        }
    }
}
