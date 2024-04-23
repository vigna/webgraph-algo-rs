use crate::{
    algo::bfv::*,
    algo::strongly_connected_components::TarjanStronglyConnectedComponents,
    prelude::*,
    utils::{argmax, argmin},
};
use anyhow::Result;
use dsi_progress_logger::*;
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

#[derive(PartialEq)]
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
    /// Creates a new instance for computing diameter and/or radius and/or all eccentricities.
    ///
    /// # Arguments
    /// - `graph`: An immutable reference to the graph.
    /// - `reversed_graph`: An immutable reference to `graph` transposed.
    /// - `output`: Which output is requested: radius, diameter, radius and diameter, or all eccentricities.
    /// - `radial_verticies`: The set of radial vertices. If [`None`], the set is automatically chosen
    /// as the set of vertices that are in the biggest strongly connected component, or that are able
    /// to reach the biggest strongly connected component.
    pub fn new(
        graph: &'a G,
        reversed_graph: &'a G,
        output: SumSweepOutputLevel,
        radial_vertices: Option<AtomicBitVec>,
    ) -> Result<Self> {
        let nn = graph.num_nodes();
        let isize_nn: isize = nn.try_into()?;
        let compute_radial_vertices = radial_vertices.is_none();
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
            upper_bound_forward_eccentricities: vec![isize_nn + 1; nn],
            lower_bound_backward_eccentricities: vec![0; nn],
            upper_bound_backward_eccentricities: vec![isize_nn + 1; nn],
            incomplete_forward_vertex: AtomicBitVec::with_value(nn, true),
            incomplete_backward_vertex: AtomicBitVec::with_value(nn, true),
            start_bridges: vec![Vec::new(); scc.number_of_components()],
            end_bridges: vec![Vec::new(); scc.number_of_components()],
            strongly_connected_components_graph: vec![Vec::new(); scc.number_of_components()],
            strongly_connected_components: scc,
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

        if compute_radial_vertices {
            ret.compute_radial_vertices()?;
        }
        ret.find_edges_through_scc()?;

        Ok(ret)
    }

    /// Performs `iterations` steps of the SumSweep heuristic, starting from vertex `start`.
    ///
    /// # Arguments
    /// - `start`: The starting vertex.
    /// - `iterations`: The number of iterations.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    pub fn sum_sweep_heuristic(
        &self,
        start: usize,
        iterations: usize,
        pl: impl ProgressLog,
    ) -> Result<()> {
        todo!()
    }

    /// Computes diameter, radius, and/or all eccentricities.
    ///
    /// Results can be accessed by methods [`Self::radius`], [`Self::diameter`], [`Self::radial_vertex`],
    /// [`Self::diametral_vertex`], [`Self::eccentricity`].
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    pub fn compute(&self, mut pl: impl ProgressLog) -> Result<()> {
        pl.start("Staring visits...");

        let max_outdegree_vertex = AtomicUsize::new(0);

        (0..self.number_of_nodes).into_par_iter().for_each(|v| {
            let outdegree = self.graph.outdegree(v);
            let mut current_max = max_outdegree_vertex.load(Ordering::Relaxed);
            while outdegree > self.graph.outdegree(current_max) {
                let result = max_outdegree_vertex.compare_exchange(
                    current_max,
                    v,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                );
                if result.is_ok() {
                    break;
                }
                current_max = max_outdegree_vertex.load(Ordering::Relaxed);
            }
        });

        pl.done();

        self.sum_sweep_heuristic(max_outdegree_vertex.load(Ordering::Relaxed), 6, pl.clone())?;

        let mut points = [self.graph.num_nodes() as f64; 6];
        let mut missing_nodes = self.find_missing_nodes();
        let mut old_missing_nodes;

        while missing_nodes > 0 {
            let step_to_perform = argmax::argmax(&points).try_into()?;

            match step_to_perform {
                0 => {
                    pl.info(format_args!("Performing all_cc_upper_bound."));
                    self.all_cc_upper_bound(pl.clone())?
                }
                1 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex maximizing the upper bound."
                    ));
                    self.step_sum_sweep(
                        argmax::filtered_argmax(
                            &self.upper_bound_forward_eccentricities,
                            &self.total_forward_distance,
                            &self.incomplete_forward_vertex,
                        )
                        .try_into()?,
                        true,
                        pl.clone(),
                    )?
                }
                2 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex minimizing the lower bound."
                    ));
                    self.step_sum_sweep(
                        argmin::filtered_argmin(
                            &self.lower_bound_forward_eccentricities,
                            &self.total_forward_distance,
                            &self.radial_vertices,
                        )
                        .try_into()?,
                        true,
                        pl.clone(),
                    )?
                }
                3 => {
                    pl.info(format_args!(
                        "Performing a backward BFS from a vertex maximizing the lower bound."
                    ));
                    self.step_sum_sweep(
                        argmax::filtered_argmax(
                            &self.upper_bound_backward_eccentricities,
                            &self.total_backward_distance,
                            &self.incomplete_backward_vertex,
                        )
                        .try_into()?,
                        false,
                        pl.clone(),
                    )?
                }
                4 => {
                    pl.info(format_args!(
                        "Performing a backward BFS, from a vertex maximizing the distance sum."
                    ));
                    self.step_sum_sweep(
                        argmax::filtered_argmax(
                            &self.total_backward_distance,
                            &self.upper_bound_backward_eccentricities,
                            &self.incomplete_backward_vertex,
                        )
                        .try_into()?,
                        false,
                        pl.clone(),
                    )?
                }
                5 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex maximizing the distance sum."
                    ));
                    self.step_sum_sweep(
                        argmax::filtered_argmax(
                            &self.total_forward_distance,
                            &self.upper_bound_forward_eccentricities,
                            &self.incomplete_forward_vertex,
                        )
                        .try_into()?,
                        false, // ???????????????????????????????????????????????????????????????????????????
                        pl.clone(),
                    )?
                }
                6.. => panic!(),
            }

            old_missing_nodes = missing_nodes;
            missing_nodes = self.find_missing_nodes();
            points[step_to_perform] = (old_missing_nodes - missing_nodes) as f64;

            for i in 0..points.len() {
                if i != step_to_perform && points[i] >= 0.0 {
                    points[i] = points[i] + 2.0 / self.iterations as f64;
                }
            }

            pl.info(format_args!(
                "Missing nodes: {}/{}.",
                missing_nodes,
                self.number_of_nodes * 2
            ));
        }

        if self.output == SumSweepOutputLevel::Radius
            || self.output == SumSweepOutputLevel::RadiusDiameter
        {
            pl.info(format_args!(
                "Radius: {} ({} iterations).",
                self.radius_upper_bound, self.radius_iterations
            ));
        }
        if self.output == SumSweepOutputLevel::Diameter
            || self.output == SumSweepOutputLevel::RadiusDiameter
        {
            pl.info(format_args!(
                "Diameter: {} ({} iterations).",
                self.diameter_lower_bound, self.diameter_iterations,
            ));
        }
        pl.done();

        Ok(())
    }

    /// Returns the radius of the graph if it has already been computed, [`None`] otherwise.
    pub fn radius(&self) -> Option<usize> {
        if self.radius_iterations == -1 {
            None
        } else {
            Some(self.radius_upper_bound)
        }
    }

    /// Returns the diameter of the graph if is has already been computed, [`None`] otherwise.
    pub fn diameter(&self) -> Option<usize> {
        if self.diameter_iterations == -1 {
            None
        } else {
            Some(self.diameter_lower_bound)
        }
    }

    /// Returns a radial vertex if it has already been computed, [`None`] otherwise.
    pub fn radial_vertex(&self) -> Option<usize> {
        if self.radius_iterations == -1 {
            None
        } else {
            Some(self.radius_vertex)
        }
    }

    /// Returns a diametral vertex if it has already been computed, [`None`] otherwise.
    pub fn diametral_vertex(&self) -> Option<usize> {
        if self.diameter_iterations == -1 {
            None
        } else {
            Some(self.diameter_vertex)
        }
    }

    /// Returns the eccentricity of a vertex if it has already been computed, [`None`] otherwise.
    ///
    /// # Arguments
    /// - `vertex`: The vertex.
    /// - `forward`: Whether to return the forward eccentricity (if `true`) or the backward
    /// eccentricity (if `false`).
    pub fn eccentricity(&self, vertex: usize, forward: bool) -> Option<usize> {
        let ecc = if forward {
            self.forward_eccentricities[vertex]
        } else {
            self.backward_eccentricities[vertex]
        };

        if ecc == -1 {
            return None;
        }

        Some(ecc.try_into().unwrap())
    }

    /// Returns the number of iterations needed to compute the radius if it has already
    /// been computed, [`None`] otherwise.
    pub fn radius_iterations(&self) -> Option<usize> {
        if self.radius_iterations == -1 {
            None
        } else {
            Some(self.radius_iterations.try_into().unwrap())
        }
    }

    /// Returns the number of iterations needed to compute the diameter if it has already
    /// been computed, [`None`] otherwise.
    pub fn diameter_iterations(&self) -> Option<usize> {
        if self.diameter_iterations == -1 {
            None
        } else {
            Some(self.diameter_iterations.try_into().unwrap())
        }
    }

    /// Returns the number of iterations needed to compute all forward eccentricities
    /// if they have already been computed, [`None`] otherwise.
    pub fn all_forward_iterations(&self) -> Option<usize> {
        if self.forward_eccentricities_iterations == -1 {
            None
        } else {
            Some(self.forward_eccentricities_iterations.try_into().unwrap())
        }
    }

    /// Returns the number of iterations needed to compute all eccentricities if they
    /// have already been computed, [`None`] otherwise.
    pub fn all_iterations(&self) -> Option<usize> {
        if self.all_eccentricities_iterations == -1 {
            None
        } else {
            Some(self.all_eccentricities_iterations.try_into().unwrap())
        }
    }

    /// Uses a heuristic to decide which is the best pivot to choose in each strongly connected
    /// component, in order to perform the [`Self::all_cc_upper_bound`] method.
    fn find_best_pivot(&self) -> Result<Vec<isize>> {
        let mut pivot = vec![-1; self.strongly_connected_components.number_of_components()];
        let components = self.strongly_connected_components.component();
        let isize_number_of_nodes = self.number_of_nodes.try_into()?;
        let mut p;
        let mut best;
        let mut current;
        let mut v = self.number_of_nodes;

        while v > 0 {
            v -= 1;
            let isize_vertex: isize = v.try_into()?;
            let usize_component: usize = components[v].try_into()?;

            p = pivot[usize_component];
            let usize_p: usize = p.try_into()?;

            if p == -1 {
                pivot[usize_component] = isize_vertex;
                continue;
            }

            current = self.lower_bound_backward_eccentricities[v]
                + self.lower_bound_forward_eccentricities[v]
                + if self.incomplete_forward_vertex.get(v, Ordering::Relaxed) {
                    0
                } else {
                    isize_number_of_nodes
                }
                + if self.incomplete_backward_vertex.get(v, Ordering::Relaxed) {
                    0
                } else {
                    isize_number_of_nodes
                };

            best = self.lower_bound_backward_eccentricities[usize_p]
                + self.lower_bound_backward_eccentricities[usize_p]
                + if self
                    .incomplete_forward_vertex
                    .get(usize_p, Ordering::Relaxed)
                {
                    0
                } else {
                    isize_number_of_nodes
                }
                + if self
                    .incomplete_backward_vertex
                    .get(usize_p, Ordering::Relaxed)
                {
                    0
                } else {
                    isize_number_of_nodes
                };

            if current < best
                || (current == best
                    && self.total_forward_distance[v] + self.total_backward_distance[v]
                        <= self.total_forward_distance[usize_p]
                            + self.total_forward_distance[usize_p])
            {
                pivot[usize_component] = isize_vertex;
            }
        }

        Ok(pivot)
    }

    /// Computes and stores in variable [`Self::radial_vertices`] the set of vertices that are
    /// either in the biggest strongly connected component or that are able to reach vertices in
    /// the biggest strongly connected component.
    fn compute_radial_vertices(&mut self) -> Result<()> {
        if self.number_of_nodes == 0 {
            return Ok(());
        }
        let component = self.strongly_connected_components.component();
        let scc_sizes = self.strongly_connected_components.compute_sizes();
        let max_size_scc = argmax::argmax(&scc_sizes);

        let mut v = self.number_of_nodes;

        while v > 0 {
            v -= 1;
            if component[v] == max_size_scc {
                break;
            }
        }
        let mut bfs = ParallelBreadthFirstVisit::with_parameters(self.reversed_graph, v, 32);
        bfs.visit_component(
            |node, _distance| self.radial_vertices.set(node, true, Ordering::Relaxed),
            v,
            &mut Option::<ProgressLogger>::None,
        )?;

        Ok(())
    }

    /// Performs a (forward or backward) BFS, updating lower bounds on the eccentricities
    /// of all visited vertices.
    ///
    /// # Arguments
    /// - `start`: The starting vertex of the BFS.
    /// - `forward`: Whether the BFS is performed following the direction of edges or
    /// in the opposite direction.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn step_sum_sweep(&self, start: usize, forward: bool, pl: impl ProgressLog) -> Result<()> {
        todo!()
    }

    /// For each edge in the DAG of strongly connected components, finds a corresponding edge
    /// in the graph. This edge is used in the [`Self::all_cc_upper_bound`] method.
    fn find_edges_through_scc(&self) -> Result<()> {
        todo!()
    }

    /// Performs a (forward or backward) BFS inside each strongly connected component, starting
    /// from the pivot.
    ///
    /// # Arguments
    /// - `pivot`: An array containing in position `i` the pivot of the `i`-th strongly connected
    /// component.
    /// - `forward`: Whether the BFS is performed following the direction of edges or
    /// in the opposite direction.
    ///
    /// # Return
    /// Two arrays.
    /// The first one contains the distance of each vertex from the pivot of its strongly connected
    /// component, while the second one contains in position `i` the eccentricity of the pivot of the
    /// `i`-th strongly connected component.
    fn compute_dist_pivot(
        &self,
        pivot: Vec<usize>,
        forward: bool,
    ) -> Result<(Vec<usize>, Vec<usize>)> {
        todo!()
    }

    /// Performs a step of the ExactSumSweep algorithm.
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn all_cc_upper_bound(&self, pl: impl ProgressLog) -> Result<()> {
        todo!()
    }

    /// Computes how many nodes are still to be processed. before outputting the result.
    fn find_missing_nodes(&self) -> usize {
        todo!()
    }
}
