use crate::{
    algo::bfv::*,
    algo::strongly_connected_components::TarjanStronglyConnectedComponents,
    prelude::*,
    utils::{argmax, argmin, closure_vec},
};
use anyhow::{Context, Result};
use dsi_progress_logger::*;
use rayon::prelude::*;
use std::sync::{
    atomic::{AtomicIsize, AtomicUsize, Ordering},
    Mutex,
};
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

type Int = isize;
const VISIT_GRANULARITY: usize = 32;

pub struct SumSweepDirectedDiameterRadius<
    'a,
    G: RandomAccessGraph + Sync,
    C: StronglyConnectedComponents<G>,
> {
    graph: &'a G,
    reversed_graph: &'a G,
    number_of_nodes: usize,
    output: SumSweepOutputLevel,
    forward_eccentricities: Vec<Int>,
    backward_eccentricities: Vec<Int>,
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
    lower_bound_forward_eccentricities: Vec<Int>,
    upper_bound_forward_eccentricities: Vec<Int>,
    lower_bound_backward_eccentricities: Vec<Int>,
    upper_bound_backward_eccentricities: Vec<Int>,
    /// Number of iterations before the radius is found.
    radius_iterations: Int,
    /// Number of iterations before the diameter is found.
    diameter_iterations: Int,
    /// Number of iterations before all forward eccentricities are found.
    forward_eccentricities_iterations: Int,
    /// Number of iterations before all eccentricities are found.
    all_eccentricities_iterations: Int,
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
    total_forward_distance: Vec<Int>,
    /// Total backward distance from already processed vertices (used as tie-break for the choice
    /// of the next vertex to process).
    total_backward_distance: Vec<Int>,
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
        let isize_nn: isize = nn
            .try_into()
            .with_context(|| "Could not convert num_nodes to isize")?;
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
            start_bridges: Vec::new(),
            end_bridges: Vec::new(),
            strongly_connected_components_graph: Vec::new(),
            strongly_connected_components: scc,
            diameter_lower_bound: 0,
            radius_upper_bound: Int::MAX as usize,
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
            ret.compute_radial_vertices()
                .with_context(|| "Could not compute radial vertices")?;
        }
        ret.find_edges_through_scc()
            .with_context(|| "Could not build scc graph")?;

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
        &mut self,
        start: usize,
        iterations: usize,
        pl: impl ProgressLog,
    ) -> Result<()> {
        pl.info(format_args!(
            "Performing initial SumSweep visit from {}.",
            start
        ));
        self.step_sum_sweep(Some(start), true, pl.clone())
            .with_context(|| "Could not perform initial SumSweep visit")?;

        for i in 2..iterations {
            if i % 2 == 0 {
                let v = argmax::filtered_argmax(
                    &self.total_backward_distance,
                    &self.lower_bound_backward_eccentricities,
                    &self.incomplete_backward_vertex,
                );
                pl.info(format_args!(
                    "Performing backwards SumSweep visit from {:?}",
                    v
                ));
                self.step_sum_sweep(v, false, pl.clone())
                    .with_context(|| format!("Could not perform backwards visit from {:?}", v))?;
            } else {
                let v = argmax::filtered_argmax(
                    &self.total_forward_distance,
                    &self.lower_bound_forward_eccentricities,
                    &self.incomplete_forward_vertex,
                );
                pl.info(format_args!(
                    "Performing forward SumSweep visit from {:?}.",
                    v
                ));
                self.step_sum_sweep(v, true, pl.clone())
                    .with_context(|| format!("Could not perform forward visit from {:?}", v))?;
            }
        }

        Ok(())
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
    pub fn compute(&mut self, mut pl: impl ProgressLog) -> Result<()> {
        if self.number_of_nodes == 0 {
            return Ok(());
        }
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

        self.sum_sweep_heuristic(max_outdegree_vertex.load(Ordering::Relaxed), 6, pl.clone())
            .with_context(|| "Could not perform first 6 iterations of SumSweep heuristic.")?;

        let mut points = [self.graph.num_nodes() as f64; 6];
        let mut missing_nodes = self
            .find_missing_nodes()
            .with_context(|| format!("Could not compute missing nodes"))?;
        let mut old_missing_nodes;

        while missing_nodes > 0 {
            let step_to_perform =
                argmax::argmax(&points).with_context(|| "Could not find step to perform")?;

            match step_to_perform {
                0 => {
                    pl.info(format_args!("Performing all_cc_upper_bound."));
                    let pivot = self
                        .find_best_pivot()
                        .with_context(|| "Could not find best pivot for allCCUpperBound")?;
                    self.all_cc_upper_bound(pivot, pl.clone())
                        .with_context(|| "Could not perform allCCUpperBound")?
                }
                1 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex maximizing the upper bound."
                    ));
                    let v = argmax::filtered_argmax(
                        &self.upper_bound_forward_eccentricities,
                        &self.total_forward_distance,
                        &self.incomplete_forward_vertex,
                    );
                    self.step_sum_sweep(v, true, pl.clone())
                        .with_context(|| format!("Could not perform forward visit from {:?}", v))?
                }
                2 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex minimizing the lower bound."
                    ));
                    let v = argmin::filtered_argmin(
                        &self.lower_bound_forward_eccentricities,
                        &self.total_forward_distance,
                        &self.radial_vertices,
                    );
                    self.step_sum_sweep(v, true, pl.clone())
                        .with_context(|| format!("Could not perform forward visit from {:?}", v))?
                }
                3 => {
                    pl.info(format_args!(
                        "Performing a backward BFS from a vertex maximizing the lower bound."
                    ));
                    let v = argmax::filtered_argmax(
                        &self.upper_bound_backward_eccentricities,
                        &self.total_backward_distance,
                        &self.incomplete_backward_vertex,
                    );
                    self.step_sum_sweep(v, false, pl.clone()).with_context(|| {
                        format!("Could not perform backwards visit from {:?}", v)
                    })?
                }
                4 => {
                    pl.info(format_args!(
                        "Performing a backward BFS, from a vertex maximizing the distance sum."
                    ));
                    let v = argmax::filtered_argmax(
                        &self.total_backward_distance,
                        &self.upper_bound_backward_eccentricities,
                        &self.incomplete_backward_vertex,
                    );
                    self.step_sum_sweep(v, false, pl.clone()).with_context(|| {
                        format!("Could not perform backwards visit from {:?}", v)
                    })?
                }
                5 => {
                    pl.info(format_args!(
                        "Performing a forward BFS, from a vertex maximizing the distance sum."
                    ));
                    let v = argmax::filtered_argmax(
                        &self.total_forward_distance,
                        &self.upper_bound_forward_eccentricities,
                        &self.incomplete_forward_vertex,
                    );
                    self.step_sum_sweep(
                        v,
                        false, // ???????????????????????????????????????????????????????????????????????????
                        pl.clone(),
                    )
                    .with_context(|| format!("Could not perform forward visit from {:?}", v))?
                }
                6.. => panic!(),
            }

            old_missing_nodes = missing_nodes;
            missing_nodes = self
                .find_missing_nodes()
                .with_context(|| format!("Could not compute missing nodes"))?;
            points[step_to_perform] = (old_missing_nodes - missing_nodes) as f64;

            for i in 0..points.len() {
                if i != step_to_perform && points[i] >= 0.0 {
                    points[i] += 2.0 / self.iterations as f64;
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
    fn find_best_pivot(&self) -> Result<Vec<usize>> {
        let mut pivot = vec![None; self.strongly_connected_components.number_of_components()];
        let components = self.strongly_connected_components.component();
        let isize_number_of_nodes = self
            .number_of_nodes
            .try_into()
            .with_context(|| "Could not convert number of scc into isize")?;

        for (v, &component) in components.iter().enumerate() {
            if let Some(p) = pivot[component] {
                let current = self.lower_bound_backward_eccentricities[v]
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

                let best = self.lower_bound_backward_eccentricities[p]
                    + self.lower_bound_backward_eccentricities[p]
                    + if self.incomplete_forward_vertex.get(p, Ordering::Relaxed) {
                        0
                    } else {
                        isize_number_of_nodes
                    }
                    + if self.incomplete_backward_vertex.get(p, Ordering::Relaxed) {
                        0
                    } else {
                        isize_number_of_nodes
                    };

                if current < best
                    || (current == best
                        && self.total_forward_distance[v] + self.total_backward_distance[v]
                            <= self.total_forward_distance[p] + self.total_forward_distance[p])
                {
                    pivot[component] = Some(v);
                }
            } else {
                pivot[component] = Some(v);
            }
        }

        Ok(pivot.into_iter().map(|x| x.unwrap()).collect())
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
        let max_size_scc =
            argmax::argmax(&scc_sizes).with_context(|| "Could not find max size scc.")?;

        let mut v = self.number_of_nodes;

        while v > 0 {
            v -= 1;
            if component[v] == max_size_scc {
                break;
            }
        }
        let mut bfs =
            ParallelBreadthFirstVisit::with_granularity(self.reversed_graph, VISIT_GRANULARITY);
        bfs.visit_component(
            |node, _distance| self.radial_vertices.set(node, true, Ordering::Relaxed),
            v,
            &mut Option::<ProgressLogger>::None,
        )
        .with_context(|| format!("Could not perform BFS from {}", v))?;

        Ok(())
    }

    /// Performs a (forward or backward) BFS, updating lower bounds on the eccentricities
    /// of all visited vertices.
    ///
    /// # Arguments
    /// - `start`: The starting vertex of the BFS. If [`None`], no visit happens.
    /// - `forward`: Whether the BFS is performed following the direction of edges or
    /// in the opposite direction.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn step_sum_sweep(
        &mut self,
        start: Option<usize>,
        forward: bool,
        mut pl: impl ProgressLog,
    ) -> Result<()> {
        if start.is_none() {
            return Ok(());
        }
        let start = start.unwrap();
        pl.item_name("nodes");
        pl.expected_updates(Some(self.number_of_nodes));
        pl.start(format!("Performing BFS starting from {}.", start));

        let lower_bound;
        let other_lower_bound;
        let upper_bound;
        let other_upper_bound;
        let other_total_distance;
        let graph;
        let eccentricities;
        let other_eccentricities;
        let incomplete;
        let other_incomplete;

        if forward {
            lower_bound = &mut self.lower_bound_forward_eccentricities;
            other_lower_bound = &self.lower_bound_backward_eccentricities;
            upper_bound = &mut self.upper_bound_forward_eccentricities;
            other_upper_bound = &self.upper_bound_backward_eccentricities;
            other_total_distance = &self.total_backward_distance;
            graph = self.graph;
            eccentricities = &mut self.forward_eccentricities;
            other_eccentricities = &self.backward_eccentricities;
            incomplete = &self.incomplete_forward_vertex;
            other_incomplete = &self.incomplete_backward_vertex;
        } else {
            lower_bound = &mut self.lower_bound_backward_eccentricities;
            other_lower_bound = &self.lower_bound_forward_eccentricities;
            upper_bound = &mut self.upper_bound_backward_eccentricities;
            other_upper_bound = &self.upper_bound_forward_eccentricities;
            other_total_distance = &self.total_forward_distance;
            graph = self.reversed_graph;
            eccentricities = &mut self.backward_eccentricities;
            other_eccentricities = &self.forward_eccentricities;
            incomplete = &self.incomplete_backward_vertex;
            other_incomplete = &self.incomplete_forward_vertex;
        }

        let max_dist = AtomicUsize::new(0);
        let current_radius_upper_bound = AtomicUsize::new(self.radius_upper_bound);
        let current_radius_vertex = AtomicUsize::new(self.radius_vertex);
        let lock = std::sync::Mutex::new(());

        let mut bfs = ParallelBreadthFirstVisit::with_granularity(graph, VISIT_GRANULARITY);

        bfs.visit_component(
            |node, distance| {
                // Safety for unsafe blocks: each node gets accessed exactly once, so no data races can happen
                let signed_distance = distance.try_into().unwrap();
                max_dist.fetch_max(distance, Ordering::Relaxed);

                let other_total_distance_ptr = other_total_distance.as_ptr() as *mut Int;
                unsafe {
                    *other_total_distance_ptr.add(node) += signed_distance;
                }
                if other_incomplete[node] && other_lower_bound[node] < signed_distance {
                    let other_lower_bound_ptr = other_lower_bound.as_ptr() as *mut Int;
                    unsafe {
                        *other_lower_bound_ptr.add(node) = signed_distance;
                    }

                    if signed_distance == other_upper_bound[node] {
                        let other_eccentricities_ptr = other_eccentricities.as_ptr() as *mut Int;
                        unsafe {
                            *other_eccentricities_ptr.add(node) = signed_distance;
                        }

                        other_incomplete.set(node, false, Ordering::Relaxed);

                        if !forward
                            && self.radial_vertices[node]
                            && distance < current_radius_upper_bound.load(Ordering::Relaxed)
                        {
                            let _l = lock.lock().unwrap();
                            if distance < current_radius_upper_bound.load(Ordering::Relaxed) {
                                current_radius_upper_bound.store(distance, Ordering::Relaxed);
                                current_radius_vertex.store(node, Ordering::Relaxed);
                            }
                        }
                    }
                }
            },
            start,
            &mut pl,
        )
        .with_context(|| format!("Could not perform BFS from {}", start))?;

        let ecc_start = max_dist.load(Ordering::Relaxed);
        let signed_ecc_start = ecc_start
            .try_into()
            .with_context(|| "Could not convert max_dist into isize")?;

        lower_bound[start] = signed_ecc_start;
        upper_bound[start] = signed_ecc_start;
        eccentricities[start] = signed_ecc_start;
        incomplete.set(start, false, Ordering::Relaxed);

        self.radius_upper_bound = current_radius_upper_bound.load(Ordering::Relaxed);
        self.radius_vertex = current_radius_vertex.load(Ordering::Relaxed);

        if self.diameter_lower_bound < ecc_start {
            self.diameter_lower_bound = ecc_start;
            self.diameter_vertex = start;
        }
        if forward && self.radial_vertices[start] && self.radius_upper_bound > ecc_start {
            self.radius_upper_bound = ecc_start;
            self.radius_vertex = start;
        }

        self.iterations += 1;
        pl.done();

        Ok(())
    }

    /// For each edge in the DAG of strongly connected components, finds a corresponding edge
    /// in the graph. This edge is used in the [`Self::all_cc_upper_bound`] method.
    fn find_edges_through_scc(&mut self) -> Result<()> {
        let node_components = self.strongly_connected_components.component();
        let number_of_scc = self.strongly_connected_components.number_of_components();
        let mut best_start = vec![None; number_of_scc];
        let mut best_end = vec![None; number_of_scc];
        let mut vertices_in_scc = vec![Vec::new(); number_of_scc];

        for (vertex, &component) in node_components.iter().enumerate() {
            vertices_in_scc[component].push(vertex);
        }

        for component in vertices_in_scc {
            let mut child_components = Vec::new();
            for v in component {
                for succ in self.graph.successors(v) {
                    let succ_component = node_components[succ];
                    if node_components[v] != node_components[succ] {
                        if best_start[succ_component].is_none() {
                            best_start[succ_component] = Some(v);
                            best_end[succ_component] = Some(succ);
                            child_components.push(succ_component);
                        } else {
                            let succ_component_best_start = best_start[succ_component].unwrap();
                            let succ_component_best_end = best_end[succ_component].unwrap();
                            if self.graph.outdegree(v) + self.reversed_graph.outdegree(succ)
                                > self.graph.outdegree(succ_component_best_end)
                                    + self.reversed_graph.outdegree(succ_component_best_start)
                            {
                                best_start[succ_component] = Some(v);
                                best_end[succ_component] = Some(succ);
                            }
                        }
                    }
                }
            }
            let number_of_children = child_components.len();
            let mut scc_vec = Vec::with_capacity(number_of_children);
            let mut start_vec = Vec::with_capacity(number_of_children);
            let mut end_vec = Vec::with_capacity(number_of_children);
            for c in child_components {
                scc_vec.push(c);
                start_vec.push(best_start[c].unwrap());
                end_vec.push(best_end[c].unwrap());
                best_start[c] = None;
            }
            self.strongly_connected_components_graph.push(scc_vec);
            self.start_bridges.push(start_vec);
            self.end_bridges.push(end_vec)
        }

        Ok(())
    }

    /// Performs a (forward or backward) BFS inside each strongly connected component, starting
    /// from the pivot.
    ///
    /// # Arguments
    /// - `pivot`: An array containing in position `i` the pivot of the `i`-th strongly connected
    /// component.
    /// - `forward`: Whether the BFS is performed following the direction of edges or
    /// in the opposite direction.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    ///
    /// # Return
    /// Two arrays.
    /// The first one contains the distance of each vertex from the pivot of its strongly connected
    /// component, while the second one contains in position `i` the eccentricity of the pivot of the
    /// `i`-th strongly connected component.
    fn compute_dist_pivot(
        &self,
        pivot: &[usize],
        forward: bool,
        mut pl: impl ProgressLog,
    ) -> Result<(Vec<isize>, Vec<isize>)> {
        let components = self.strongly_connected_components.component();
        let ecc_pivot = closure_vec(
            || AtomicIsize::new(0),
            self.strongly_connected_components.number_of_components(),
        );
        let dist_pivot = closure_vec(|| AtomicIsize::new(-1), self.number_of_nodes);
        let graph = if forward {
            self.graph
        } else {
            self.reversed_graph
        };
        let mut bfs = ParallelBreadthFirstVisit::with_granularity(graph, VISIT_GRANULARITY);

        pl.item_name("nodes");
        pl.expected_updates(Some(self.number_of_nodes));
        if forward {
            pl.start("Computing forward dist pivots");
        } else {
            pl.start("Computing backwards dist pivots");
        }

        for &p in pivot {
            dist_pivot[p].store(0, Ordering::Relaxed);

            bfs.visit_component(
                |node, distance| {
                    let signed_distance = distance.try_into().unwrap();
                    if components[node] == components[p]
                        && dist_pivot[node].load(Ordering::Relaxed) == -1
                    {
                        dist_pivot[node].store(signed_distance, Ordering::Relaxed);
                        ecc_pivot[components[p]].store(signed_distance, Ordering::Relaxed);
                    }
                },
                p,
                &mut pl,
            )
            .with_context(|| format!("Could not perform visit from {}", p))?;
        }

        pl.done();

        let usize_dist_pivot = unsafe {
            let mut clone = std::mem::ManuallyDrop::new(dist_pivot);
            Vec::from_raw_parts(
                clone.as_mut_ptr() as *mut isize,
                clone.len(),
                clone.capacity(),
            )
        };
        let usize_ecc_pivot = unsafe {
            let mut clone = std::mem::ManuallyDrop::new(ecc_pivot);
            Vec::from_raw_parts(
                clone.as_mut_ptr() as *mut isize,
                clone.len(),
                clone.capacity(),
            )
        };

        Ok((usize_dist_pivot, usize_ecc_pivot))
    }

    /// Performs a step of the ExactSumSweep algorithm.
    ///
    /// # Arguments
    /// - `pivot`: An array containing in position `i` the pivot of the `i`-th strongly connected component.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn all_cc_upper_bound(&mut self, pivot: Vec<usize>, pl: impl ProgressLog) -> Result<()> {
        let dist_ecc_f = self
            .compute_dist_pivot(&pivot, true, pl.clone())
            .with_context(|| format!("Could not compute forward dist pivot"))?;
        let dist_ecc_b = self
            .compute_dist_pivot(&pivot, false, pl.clone())
            .with_context(|| format!("Could not compute backward dist pivot"))?;
        let dist_pivot_f = dist_ecc_f.0;
        let mut ecc_pivot_f = dist_ecc_f.1;
        let dist_pivot_b = dist_ecc_b.0;
        let mut ecc_pivot_b = dist_ecc_b.1;
        let components = self.strongly_connected_components.component();

        pl.info(format_args!("Computing forward eccentricities for pivots"));

        for (c, &p) in pivot.iter().enumerate() {
            for i in 0..self.strongly_connected_components_graph[c].len() {
                let next_c = self.strongly_connected_components_graph[c][i];
                let start = self.start_bridges[c][i];
                let end = self.end_bridges[c][i];

                ecc_pivot_f[c] = std::cmp::max(
                    ecc_pivot_f[c],
                    dist_pivot_f[start] + 1 + dist_pivot_b[end] + ecc_pivot_f[next_c],
                );

                if ecc_pivot_f[c] >= self.upper_bound_forward_eccentricities[p] {
                    ecc_pivot_f[c] = self.upper_bound_forward_eccentricities[p];
                    break;
                }
            }
        }

        pl.info(format_args!(
            "Coumputing backwards eccentricities for pivots"
        ));

        for c in 0..self.strongly_connected_components.number_of_components() {
            for i in 0..self.strongly_connected_components_graph[c].len() {
                let next_c = self.strongly_connected_components_graph[c][i];
                let start = self.start_bridges[c][i];
                let end = self.end_bridges[c][i];

                ecc_pivot_b[next_c] = std::cmp::max(
                    ecc_pivot_b[next_c],
                    dist_pivot_f[start] + 1 + dist_pivot_b[end] + ecc_pivot_b[c],
                );

                if ecc_pivot_b[next_c] >= self.upper_bound_forward_eccentricities[pivot[next_c]] {
                    ecc_pivot_b[next_c] = self.upper_bound_backward_eccentricities[pivot[next_c]];
                }
            }
        }

        let lock = Mutex::new(());
        let current_radius_upper_bound =
            AtomicIsize::new(self.radius_upper_bound.try_into().with_context(|| {
                format!("Could not convert self.radius_upper_bound into isize")
            })?);
        let current_radial_vertex = AtomicUsize::new(self.radius_vertex);

        (0..self.number_of_nodes).into_par_iter().for_each(|node| {
            // Safety for unsafe blocks: each node gets accessed exactly once, so no data races can happen
            let f_ecc_upper_bound_ptr =
                self.upper_bound_forward_eccentricities.as_ptr() as *mut Int;
            let f_ecc_ptr = self.forward_eccentricities.as_ptr() as *mut Int;
            let b_ecc_upper_bound_ptr =
                self.upper_bound_backward_eccentricities.as_ptr() as *mut Int;
            let b_ecc_ptr = self.backward_eccentricities.as_ptr() as *mut Int;

            unsafe {
                *f_ecc_upper_bound_ptr.add(node) = std::cmp::min(
                    self.upper_bound_forward_eccentricities[node],
                    dist_pivot_b[node] + ecc_pivot_f[components[node]],
                )
            }

            if self.upper_bound_forward_eccentricities[node]
                == self.lower_bound_forward_eccentricities[node]
            {
                // We do not have to check whether self.forward_eccentricities[node]=D, because
                // self.lower_bound_forward_eccentricities[node] = d(w, v) for some w from which
                // we have already performed a BFS.
                let new_ecc = self.upper_bound_forward_eccentricities[node];
                self.incomplete_forward_vertex
                    .set(node, false, Ordering::Relaxed);

                unsafe {
                    *f_ecc_ptr.add(node) = new_ecc;
                }

                if self.radial_vertices[node]
                    && new_ecc < current_radius_upper_bound.load(Ordering::Relaxed)
                {
                    let _l = lock.lock().unwrap();
                    if new_ecc < current_radius_upper_bound.load(Ordering::Relaxed) {
                        current_radius_upper_bound.store(new_ecc, Ordering::Relaxed);
                        current_radial_vertex.store(node, Ordering::Relaxed);
                    }
                }
            }

            unsafe {
                *b_ecc_upper_bound_ptr.add(node) = std::cmp::min(
                    self.upper_bound_backward_eccentricities[node],
                    dist_pivot_f[node] + ecc_pivot_b[components[node]],
                )
            }

            if self.upper_bound_backward_eccentricities[node]
                == self.lower_bound_backward_eccentricities[node]
            {
                self.incomplete_backward_vertex
                    .set(node, false, Ordering::Relaxed);

                unsafe {
                    *b_ecc_ptr.add(node) = self.upper_bound_backward_eccentricities[node];
                }
            }
        });

        self.radius_vertex = current_radial_vertex.load(Ordering::Relaxed);
        self.radius_upper_bound = current_radius_upper_bound
            .load(Ordering::Relaxed)
            .try_into()
            .with_context(|| format!("Could not convert AtomisIsize into usize"))?;

        self.iterations += 3;

        Ok(())
    }

    /// Computes how many nodes are still to be processed. before outputting the result.
    fn find_missing_nodes(&mut self) -> Result<usize> {
        let missing_r = AtomicUsize::new(0);
        let missing_df = AtomicUsize::new(0);
        let missing_db = AtomicUsize::new(0);
        let missing_all_forward = AtomicUsize::new(0);
        let missing_all_backward = AtomicUsize::new(0);
        let signed_radius_upper_bound = self
            .radius_upper_bound
            .try_into()
            .with_context(|| format!("Could not convert {} into isize", self.radius_upper_bound))?;
        let signed_diameter_lower_bound =
            self.diameter_lower_bound.try_into().with_context(|| {
                format!("Could not convert {} into isize", self.diameter_lower_bound)
            })?;

        (0..self.number_of_nodes).into_par_iter().for_each(|node| {
            if self.incomplete_forward_vertex[node] {
                missing_all_forward.fetch_add(1, Ordering::Relaxed);
                if self.upper_bound_forward_eccentricities[node] > signed_diameter_lower_bound {
                    missing_df.fetch_add(1, Ordering::Relaxed);
                }
                if self.radial_vertices[node]
                    && self.lower_bound_forward_eccentricities[node] < signed_radius_upper_bound
                {
                    missing_r.fetch_add(1, Ordering::Relaxed);
                }
            }
            if self.incomplete_backward_vertex[node] {
                missing_all_backward.fetch_add(1, Ordering::Relaxed);
                if self.upper_bound_backward_eccentricities[node] > signed_diameter_lower_bound {
                    missing_db.fetch_add(1, Ordering::Relaxed);
                }
            }
        });

        let signed_iterations = self
            .iterations
            .try_into()
            .with_context(|| format!("Could not convert iterations to isize"))?;
        let missing_r = missing_r.load(Ordering::Relaxed);
        let missing_df = missing_df.load(Ordering::Relaxed);
        let missing_db = missing_db.load(Ordering::Relaxed);
        let missing_all_forward = missing_all_forward.load(Ordering::Relaxed);
        let missing_all_backward = missing_all_backward.load(Ordering::Relaxed);

        if missing_r == 0 && self.radius_iterations == -1 {
            self.radius_iterations = signed_iterations;
        }
        if (missing_df == 0 || missing_db == 0) && self.diameter_iterations == -1 {
            self.diameter_iterations = signed_iterations;
        }
        if missing_all_forward == 0 && self.forward_eccentricities_iterations == -1 {
            self.forward_eccentricities_iterations = signed_iterations;
        }
        if missing_all_forward == 0 && missing_all_backward == 0 {
            self.all_eccentricities_iterations = signed_iterations;
        }

        match self.output {
            SumSweepOutputLevel::Radius => Ok(missing_r),
            SumSweepOutputLevel::Diameter => Ok(std::cmp::min(missing_df, missing_db)),
            SumSweepOutputLevel::RadiusDiameter => {
                Ok(missing_r + std::cmp::min(missing_df, missing_db))
            }
            SumSweepOutputLevel::AllForward => Ok(missing_all_forward),
            SumSweepOutputLevel::All => Ok(missing_all_backward + missing_all_forward),
        }
    }
}
