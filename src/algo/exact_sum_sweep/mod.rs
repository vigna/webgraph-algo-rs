//! An implementation of the [ExactSumSweep algorithm](DirExactSumSweep).
//!
//! The algorithm has been described by Michele Borassi, Pierluigi Crescenzi,
//! Michel Habib, Walter A. Kosters, Andrea Marino, and Frank W. Takes in “[Fast
//! diameter and radius BFS-based computation in (weakly connected) real-world
//! graphs–With an application to the six degrees of separation
//! games](https://www.sciencedirect.com/science/article/pii/S0304397515001644)”,
//! *Theoretical Computer Science*, 586:59–80, Elsevier, 2015. [DOI
//! 10.1016/j.tcs.2015.02.033](https://doi.org/10.1016/j.tcs.2015.02.033).

/// The possible outputs of [ExactSumSweep](DirExactSumSweep)
///
/// Note that the items have a slightly different meaning for the
/// [`directed`](`DirExactSumSweep`) and the [`undirected`](`UndirExactSumSweep`)
/// case.
//#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]

pub trait OutputLevel: Sized {
    type DirectedOutput;
    type UndirectedOutput;

    fn new_directed<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::DirectedOutput
    where
        Self: Sync;
    fn new_undirected<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::UndirectedOutput
    where
        Self: Sync;
}
/// Compute all the eccentricities of the graph.
///
/// This variant is equivalent to [`AllForward`](`Self::AllForward`) in the undirected case.
pub struct All {}

impl OutputLevel for All {
    type DirectedOutput = directed::All;
    type UndirectedOutput = undirected::All;

    fn new_directed<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::DirectedOutput
    where
        Self: OutputLevel,
    {
        Self::DirectedOutput {
            // TODO
            forward_eccentricities: computer.forward_low.clone().into_boxed_slice(),
            backward_eccentricities: computer.backward_low.clone().into_boxed_slice(),
            diameter: computer.diameter().expect("Diameter should be computed"),
            radius: computer.radius().expect("Radius should be computed"),
            diametral_vertex: computer
                .diametral_vertex()
                .expect("Diametral vertex should not be None"),
            radial_vertex: computer
                .radial_vertex()
                .expect("Radial vertex should not be None"),
            radius_iterations: computer
                .radius_iterations()
                .expect("Radius iteations should not be None"),
            diameter_iterations: computer
                .diameter_iterations()
                .expect("Diameter iterations should not be None"),
            forward_iterations: computer
                .all_forward_iterations()
                .expect("Forward iterations should not be None"),
            all_iterations: computer
                .all_iterations()
                .expect("All iterations should not be None"),
        }
    }

    fn new_undirected<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::UndirectedOutput {
        Self::UndirectedOutput {
            eccentricities: computer.forward_low.clone().into_boxed_slice(),
            diameter: computer.diameter().expect("Diameter should be computed"),
            radius: computer.radius().expect("Radius should be computed"),
            diametral_vertex: computer
                .diametral_vertex()
                .expect("Diametral vertex should not be None"),
            radial_vertex: computer
                .radial_vertex()
                .expect("Radial vertex should not be None"),
            radius_iterations: computer
                .radius_iterations()
                .expect("Radius iteations should not be None"),
            diameter_iterations: computer
                .diameter_iterations()
                .expect("Diameter iterations should not be None"),
            iterations: computer
                .all_forward_iterations()
                .expect("Forward iterations should not be None"),
        }
    }
}

/// Compute all the forward eccentricities of the graph.
pub struct AllForward {}

impl OutputLevel for AllForward {
    type DirectedOutput = directed::AllForward;
    type UndirectedOutput = undirected::All;

    fn new_directed<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::DirectedOutput {
        Self::DirectedOutput {
            forward_eccentricities: computer.forward_low.clone().into_boxed_slice(),
            diameter: computer.diameter().expect("Diameter should be computed"),
            radius: computer.radius().expect("Radius should be computed"),
            diametral_vertex: computer
                .diametral_vertex()
                .expect("Diametral vertex should not be None"),
            radial_vertex: computer
                .radial_vertex()
                .expect("Radial vertex should not be None"),
            radius_iterations: computer
                .radius_iterations()
                .expect("Radius iteations should not be None"),
            diameter_iterations: computer
                .diameter_iterations()
                .expect("Diameter iterations should not be None"),
            forward_iterations: computer
                .all_forward_iterations()
                .expect("Forward iterations should not be None"),
        }
    }

    fn new_undirected<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::UndirectedOutput {
        Self::UndirectedOutput {
            eccentricities: computer.forward_low.clone().into_boxed_slice(),
            diameter: computer.diameter().expect("Diameter should be computed"),
            radius: computer.radius().expect("Radius should be computed"),
            diametral_vertex: computer
                .diametral_vertex()
                .expect("Diametral vertex should not be None"),
            radial_vertex: computer
                .radial_vertex()
                .expect("Radial vertex should not be None"),
            radius_iterations: computer
                .radius_iterations()
                .expect("Radius iteations should not be None"),
            diameter_iterations: computer
                .diameter_iterations()
                .expect("Diameter iterations should not be None"),
            iterations: computer
                .all_forward_iterations()
                .expect("Forward iterations should not be None"),
        }
    }
}

/// Computes both the diameter and the radius of the graph.
pub struct RadiusDiameter {}

impl OutputLevel for RadiusDiameter {
    type DirectedOutput = directed::RadiusDiameter;
    type UndirectedOutput = undirected::RadiusDiameter;

    fn new_directed<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::DirectedOutput {
        Self::DirectedOutput {
            diameter: computer.diameter().expect("Diameter should be computed"),
            radius: computer.radius().expect("Radius should be computed"),
            diametral_vertex: computer
                .diametral_vertex()
                .expect("Diametral vertex should not be None"),
            radial_vertex: computer
                .radial_vertex()
                .expect("Radial vertex should not be None"),
            radius_iterations: computer
                .radius_iterations()
                .expect("Radius iteations should not be None"),
            diameter_iterations: computer
                .diameter_iterations()
                .expect("Diameter iterations should not be None"),
        }
    }

    fn new_undirected<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::UndirectedOutput {
        Self::UndirectedOutput {
            diameter: computer.diameter().expect("Diameter should be computed"),
            radius: computer.radius().expect("Radius should be computed"),
            diametral_vertex: computer
                .diametral_vertex()
                .expect("Diametral vertex should not be None"),
            radial_vertex: computer
                .radial_vertex()
                .expect("Radial vertex should not be None"),
        }
    }
}

/// Computes the diameter of the graph.
pub struct Diameter {}

impl OutputLevel for Diameter {
    type DirectedOutput = directed::Diameter;
    type UndirectedOutput = undirected::Diameter;

    fn new_directed<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::DirectedOutput {
        Self::DirectedOutput {
            diameter: computer.diameter().expect("Diameter should be computed"),
            diametral_vertex: computer
                .diametral_vertex()
                .expect("Diametral vertex should not be None"),
            diameter_iterations: computer
                .diameter_iterations()
                .expect("Diameter iterations should not be None"),
        }
    }

    fn new_undirected<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::UndirectedOutput {
        Self::UndirectedOutput {
            diameter: computer.diameter().expect("Diameter should be computed"),
            diametral_vertex: computer
                .diametral_vertex()
                .expect("Diametral vertex should not be None"),
            diameter_iterations: computer
                .diameter_iterations()
                .expect("Diameter iterations should not be None"),
        }
    }
}
/// Computers the radius of the graph.
pub struct Radius {}

impl OutputLevel for Radius {
    type DirectedOutput = directed::Radius;
    type UndirectedOutput = undirected::Radius;

    fn new_directed<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::DirectedOutput {
        Self::DirectedOutput {
            radius: computer.radius().expect("Radius should be computed"),
            radial_vertex: computer
                .radial_vertex()
                .expect("Radial vertex should not be None"),
            radius_iterations: computer
                .radius_iterations()
                .expect("Radius iteations should not be None"),
        }
    }

    fn new_undirected<
        G1: RandomAccessGraph + Sync,
        G2: RandomAccessGraph + Sync,
        SCC: StronglyConnectedComponents + Sync,
        V1: Parallel<Event> + Sync,
        C2: Parallel<Event> + Sync,
    >(
        computer: DirExactSumSweepComputer<Self, G1, G2, SCC, V1, C2>,
    ) -> Self::UndirectedOutput {
        Self::UndirectedOutput {
            radius: computer.radius().expect("Radius should be computed"),
            radial_vertex: computer
                .radial_vertex()
                .expect("Radial vertex should not be None"),
            radius_iterations: computer
                .radius_iterations()
                .expect("Radius iteations should not be None"),
        }
    }
}

pub mod directed;
mod scc_graph;
pub mod undirected;

use super::{
    traits::StronglyConnectedComponents,
    visits::{breadth_first::Event, Parallel},
};
use crate::algo::exact_sum_sweep::directed::DirExactSumSweepComputer;
use webgraph::prelude::RandomAccessGraph;
