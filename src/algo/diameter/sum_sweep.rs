use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

pub enum SumSweepOutputLevel {
    All,
    AllForward,
    Diameter,
    Radius,
    RadiusDiameter,
}

pub struct SumSweepDirectedDiameterRadius<'a, G: RandomAccessGraph> {
    graph: &'a G,
    reversed_graph: &'a G,
    number_of_nodes: usize,
    output: SumSweepOutputLevel,
    forward_eccentricities: Vec<isize>,
    backward_eccentricities: Vec<isize>,
    incomplete_forward_vertex: BitVec,
    incomplete_backward_vertex: BitVec,
    radial_vertices: BitVec,
    diameter_lower_bound: usize,
    radius_upper_bound: usize,
    /// A vertex whose eccentricity equals the diameter.
    diameter_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    radius_vertex: usize,
    /// Number of iterations performed until now.
    iterations: isize,
}
