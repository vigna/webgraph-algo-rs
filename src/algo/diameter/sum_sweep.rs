use crate::{
    algo::bfv::*, algo::strongly_connected_components::TarjanStronglyConnectedComponents,
    prelude::*, utils::argmax,
};
use dsi_progress_logger::*;
use std::sync::atomic::Ordering;
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

pub enum SumSweepOutputLevel {
    All,
    AllForward,
    Diameter,
    Radius,
    RadiusDiameter,
}

pub struct SumSweepDirectedDiameterRadius<
    'a,
    G: RandomAccessGraph + Sync,
    C: StronglyConnectedComponents<G>,
> {
    graph: &'a G,
    reversed_graph: &'a G,
    number_of_nodes: usize,
    output: SumSweepOutputLevel,
    forward_eccentricities: Vec<isize>,
    backward_eccentricities: Vec<isize>,
    incomplete_forward_vertex: AtomicBitVec,
    incomplete_backward_vertex: AtomicBitVec,
    radial_vertices: AtomicBitVec,
    diameter_lower_bound: usize,
    radius_upper_bound: usize,
    /// A vertex whose eccentricity equals the diameter.
    diameter_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    radius_vertex: usize,
    /// Number of iterations performed until now.
    iterations: usize,
    lower_bound_forward_eccentricities: Vec<isize>,
    upper_bound_forward_eccentricities: Vec<isize>,
    lower_bound_backward_eccentricities: Vec<isize>,
    upper_bound_backward_eccentricities: Vec<isize>,
    /// Number of iterations before the radius is found.
    radius_iterations: isize,
    /// Number of iterations before the diameter is found.
    diameter_iterations: isize,
    /// Number of iterations before all forward eccentricities are found.
    forward_eccentricities_iterations: isize,
    /// Number of iterations before all eccentricities are found.
    all_eccentricities_iterations: isize,
    strongly_connected_components: C,
    /// The strongly connected components diagram.
    strongly_connected_components_graph: Vec<Vec<usize>>,
    /// For each edge in [`Self::strongly_connected_components_graph`], the start vertex of a
    /// corresponding edge in the graph.
    start_bridges: Vec<Vec<usize>>,
    /// For each edge in [`Self::strongly_connected_components_graph`], the end vertex of a
    /// corresponding edge in the graph.
    end_bridges: Vec<Vec<usize>>,
    /// Total forward distance from already processed vertices (used as tie-break for the choice
    /// of the next vertex to process).
    total_forward_distance: Vec<isize>,
    /// Total backward distance from already processed vertices (used as tie-break for the choice
    /// of the next vertex to process).
    total_backward_distance: Vec<isize>,
}

impl<'a, G: RandomAccessGraph + Sync>
    SumSweepDirectedDiameterRadius<'a, G, TarjanStronglyConnectedComponents<G>>
{
    fn new(
        graph: &G,
        reversed_graph: &G,
        output: SumSweepOutputLevel,
        radial_vertices: Option<AtomicBitVec>,
    ) -> SumSweepDirectedDiameterRadius<'a, G, TarjanStronglyConnectedComponents<G>> {
        let nn = graph.num_nodes();
        let scc = TarjanStronglyConnectedComponents::compute(
            graph,
            false,
            Option::<ProgressLogger>::None,
        );
        let acc_radial = if let Some(r) = radial_vertices {
            if r.len() != nn {
                panic!("The size of the array of acceptable vertices must be equal to the number of nodes in the graph");
            }
            r
        } else {
            AtomicBitVec::new(nn)
        };

        debug_assert_eq!(graph.num_nodes(), reversed_graph.num_nodes());
        debug_assert_eq!(graph.num_arcs(), reversed_graph.num_arcs());

        let mut ret = SumSweepDirectedDiameterRadius {
            graph,
            reversed_graph,
            number_of_nodes: nn,
            forward_eccentricities: vec![-1; nn],
            backward_eccentricities: vec![-1; nn],
            total_forward_distance: vec![0; nn],
            total_backward_distance: vec![0; nn],
            lower_bound_forward_eccentricities: vec![0; nn],
            upper_bound_forward_eccentricities: vec![nn.try_into().unwrap() + 1; nn],
            lower_bound_backward_eccentricities: vec![0; nn],
            upper_bound_backward_eccentricities: vec![nn.try_into().unwrap() + 1; nn],
            incomplete_forward_vertex: AtomicBitVec::with_value(nn, true),
            incomplete_backward_vertex: AtomicBitVec::with_value(nn, true),
            strongly_connected_components: scc,
            start_bridges: vec![Vec::new(); scc.number_of_components()],
            end_bridges: vec![Vec::new(); scc.number_of_components()],
            strongly_connected_components_graph: vec![Vec::new(); scc.number_of_components()],
            diameter_lower_bound: 0,
            radius_upper_bound: usize::MAX,
            output,
            radius_iterations: -1,
            diameter_iterations: -1,
            all_eccentricities_iterations: -1,
            forward_eccentricities_iterations: -1,
            iterations: 0,
            radial_vertices: acc_radial,
            radius_vertex: 0,
            diameter_vertex: 0,
        };

        if radial_vertices.is_none() {
            ret.compute_radial_vertices();
        }
        ret.find_edges_through_scc();

        ret
    }

    fn compute_radial_vertices(&mut self) {
        if self.number_of_nodes == 0 {
            return;
        }
        let component = self.strongly_connected_components.component();
        let scc_sizes = self.strongly_connected_components.compute_sizes();
        let max_size_scc = argmax(&scc_sizes);

        let mut v = self.number_of_nodes;

        while v > 0 {
            if component[v] == max_size_scc {
                break;
            }
            v -= 1;
        }
        let mut bfs = ParallelBreadthFirstVisit::with_parameters(self.reversed_graph, v, 32);
        bfs.visit_component(
            |node, distance| self.radial_vertices.set(node, true, Ordering::Relaxed),
            v,
            &mut Option::<ProgressLogger>::None,
        );
    }

    fn find_edges_through_scc(&mut self) {}
}
