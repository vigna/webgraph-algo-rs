use crate::{
    algo::{bfv::BFVBuilder, diameter::SumSweepOutputLevel},
    prelude::*,
    utils::{math, MmapSlice},
};
use anyhow::{Context, Result};
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use rayon::prelude::*;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    RwLock,
};
use sux::bits::AtomicBitVec;
use webgraph::traits::RandomAccessGraph;

const VISIT_GRANULARITY: usize = 32;

#[inline(always)]
fn get_first_two<T>(mut iter: impl Iterator<Item = T>) -> Option<(T, T)> {
    if let Some(first) = iter.next() {
        iter.next().map(|second| (first, second))
    } else {
        None
    }
}

pub struct SumSweepUndirectedDiameterRadius<'a, G: RandomAccessGraph + Sync> {
    graph: &'a G,
    number_of_nodes: usize,
    output: SumSweepOutputLevel,
    diameter_lower_bound: usize,
    radius_upper_bound: usize,
    /// A vertex whose eccentricity equals the diameter.
    diameter_vertex: usize,
    /// A vertex whose eccentrivity equals the radius.
    radius_vertex: usize,
    /// Number of iterations performed until now.
    iterations: usize,
    lower_bound_eccentricities: MmapSlice<usize>,
    upper_bound_eccentricities: MmapSlice<usize>,
    /// Number of iterations before the radius is found.
    radius_iterations: Option<NonMaxUsize>,
    /// Number of iterations before the diameter is found.
    diameter_iterations: Option<NonMaxUsize>,
    /// Number of iterations before all eccentricities are found.
    all_eccentricities_iterations: Option<NonMaxUsize>,
    /// Total distance from already processed vertices (used as tie-break for the choice
    /// of the next vertex to process).
    total_distance: MmapSlice<usize>,
}

impl<'a, G: RandomAccessGraph + Sync> SumSweepUndirectedDiameterRadius<'a, G> {
    pub fn new(
        graph: &'a G,
        output: SumSweepOutputLevel,
        options: TempMmapOptions,
        pl: impl ProgressLog,
    ) -> Result<Self> {
        let nn = graph.num_nodes();

        pl.info(format_args!("Initializing data structure"));

        let lower_slice = MmapSlice::from_value(0, nn, options.clone())
            .with_context(|| "Cannot create lower bound slice")?;
        let upper_slice = MmapSlice::from_value(usize::MAX, nn, options.clone())
            .with_context(|| "Cannot create upper bound slice")?;
        let total_slice = MmapSlice::from_value(0, nn, options.clone())
            .with_context(|| "Cannot create total distance slice")?;

        Ok(Self {
            graph,
            number_of_nodes: nn,
            output,
            diameter_lower_bound: 0,
            radius_upper_bound: usize::MAX,
            diameter_vertex: 0,
            radius_vertex: 0,
            iterations: 0,
            lower_bound_eccentricities: lower_slice,
            upper_bound_eccentricities: upper_slice,
            radius_iterations: None,
            diameter_iterations: None,
            all_eccentricities_iterations: None,
            total_distance: total_slice,
        })
    }

    /// Returns the radius of the graph if it has already been computed, [`None`] otherwise.
    pub fn radius(&self) -> Option<usize> {
        if self.radius_iterations.is_none() {
            None
        } else {
            Some(self.radius_upper_bound)
        }
    }

    /// Returns the diameter of the graph if is has already been computed, [`None`] otherwise.
    pub fn diameter(&self) -> Option<usize> {
        if self.diameter_iterations.is_none() {
            None
        } else {
            Some(self.diameter_lower_bound)
        }
    }

    /// Returns a radial vertex if it has already been computed, [`None`] otherwise.
    pub fn radial_vertex(&self) -> Option<usize> {
        if self.radius_iterations.is_none() {
            None
        } else {
            Some(self.radius_vertex)
        }
    }

    /// Returns a diametral vertex if it has already been computed, [`None`] otherwise.
    pub fn diametral_vertex(&self) -> Option<usize> {
        if self.diameter_iterations.is_none() {
            None
        } else {
            Some(self.diameter_vertex)
        }
    }

    /// Returns the eccentricity of a vertex if it has already been computed, [`None`] otherwise.
    ///
    /// # Arguments
    /// - `vertex`: The vertex.
    pub fn eccentricity(&self, vertex: usize) -> Option<usize> {
        self.vertex_eccentricity(vertex)
    }

    /// Returns the number of iterations needed to compute the radius if it has already
    /// been computed, [`None`] otherwise.
    pub fn radius_iterations(&self) -> Option<usize> {
        self.radius_iterations.map(|v| v.into())
    }

    /// Returns the number of iterations needed to compute the diameter if it has already
    /// been computed, [`None`] otherwise.
    pub fn diameter_iterations(&self) -> Option<usize> {
        self.diameter_iterations.map(|v| v.into())
    }

    /// Returns the number of iterations needed to compute all eccentricities if they
    /// have already been computed, [`None`] otherwise.
    pub fn all_iterations(&self) -> Option<usize> {
        self.all_eccentricities_iterations.map(|v| v.into())
    }

    fn incomplete_vertex(&self, index: usize) -> bool {
        self.lower_bound_eccentricities[index] != self.upper_bound_eccentricities[index]
    }

    fn vertex_eccentricity(&self, index: usize) -> Option<usize> {
        if self.incomplete_vertex(index) {
            None
        } else {
            debug_assert_eq!(
                self.lower_bound_eccentricities[index],
                self.upper_bound_eccentricities[index]
            );
            Some(self.lower_bound_eccentricities[index])
        }
    }

    /// Performs a BFS, updating upper and lower bounds on the eccentricities
    /// of all visited nodes.
    ///
    /// # Arguments
    /// - `start`: The starting vertex of the BFS. If [`None`], no visit happens.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn step_sum_sweep(&mut self, start: Option<usize>, mut pl: impl ProgressLog) -> Result<()> {
        if start.is_none() {
            return Ok(());
        }
        let start = start.unwrap();
        if self.graph.outdegree(start) == 0 {
            self.radius_upper_bound = 0;
            self.radius_vertex = start;
            self.lower_bound_eccentricities[start] = 0;
            self.upper_bound_eccentricities[start] = 0;
            return Ok(());
        }

        let first_branch = AtomicBitVec::new(self.number_of_nodes);
        let mut dist: Vec<Option<NonMaxUsize>> = vec![None; self.number_of_nodes];

        // If the BFS starts with a path, consider it separately
        let mut v = start;
        let mut w;
        let mut start_len = 0;
        dist[v] = Some(NonMaxUsize::ZERO);

        if self.graph.outdegree(v) == 1 {
            w = v;
            v = self.graph.successors(start).into_iter().next().unwrap();

            dist[v] = Some(NonMaxUsize::ONE);
            start_len += 1;

            while self.graph.outdegree(v) == 2 {
                let (first, second) = get_first_two(self.graph.successors(v).into_iter())
                    .expect("self.graph.successors(v) should yield at least two elements");
                let old = w;

                w = v;

                if first == old {
                    v = second;
                } else {
                    v = first;
                }

                let dist_w: usize = dist[w].unwrap().into();
                dist[v] =
                    Some(NonMaxUsize::new(dist_w + 1).expect("dist should never equal usize::MAX"));
                start_len += 1;
            }
        }

        if let Some((first, second)) = get_first_two(self.graph.successors(v).into_iter()) {
            if dist[first].is_none() {
                first_branch.set(first, true, Ordering::Relaxed);
            } else {
                first_branch.set(second, true, Ordering::Relaxed);
            }
        }

        pl.item_name("nodes");
        pl.display_memory(false);
        pl.expected_updates(None);
        pl.start(format!("Performing BFS from {}", start));

        let mut visit = BFVBuilder::new_parallel_fast_callback(self.graph)
            .granularity(VISIT_GRANULARITY)
            .build();
        let ecc_not_first_branch = AtomicUsize::new(0);
        let max_dist = AtomicUsize::new(0);
        let dist_mut = dist.as_mut_slice_of_cells();

        visit
            .visit_from_node(
                |node, parent, _, _| {
                    // Safety for unsafe blocks: each node is visited exactly once. Parents can never
                    // be out of sync.
                    if dist_mut[node].read().is_none() {
                        first_branch.set(
                            node,
                            first_branch[node] || first_branch[parent],
                            Ordering::Relaxed,
                        );

                        let parent_dist: usize = dist_mut[parent].read().unwrap().into();
                        unsafe {
                            dist_mut.write_once(
                                node,
                                Some(
                                    NonMaxUsize::new(parent_dist + 1)
                                        .expect("dist should never equal usize::MAX"),
                                ),
                            );
                        }
                    }

                    if !first_branch[node] {
                        ecc_not_first_branch.fetch_add(1, Ordering::Relaxed);
                    }

                    max_dist.fetch_max(dist_mut[node].read().unwrap().into(), Ordering::Relaxed);
                },
                v,
                &mut pl,
            )
            .with_context(|| format!("Could not perform parallel BFV from {}", v))?;

        let max_dist: isize = max_dist
            .load(Ordering::Relaxed)
            .try_into()
            .with_context(|| {
                format!(
                    "Cannot convert {} to isize",
                    max_dist.load(Ordering::Relaxed)
                )
            })?;
        let ecc_not_first_branch: isize = ecc_not_first_branch
            .load(Ordering::Relaxed)
            .try_into()
            .with_context(|| {
            format!(
                "Cannot convert {} to isize",
                ecc_not_first_branch.load(Ordering::Relaxed)
            )
        })?;

        let radius = RwLock::new((self.radius_upper_bound, self.radius_vertex));
        let diameter = RwLock::new((self.diameter_lower_bound, self.diameter_vertex));

        let total_distance = self.total_distance.as_mut_slice_of_cells();
        let lower_bound_eccentricities = self.lower_bound_eccentricities.as_mut_slice_of_cells();
        let upper_bound_eccentricities = self.upper_bound_eccentricities.as_mut_slice_of_cells();

        // Update bounds
        (0..self.number_of_nodes).into_par_iter().for_each(|node| {
            // Safety for unsafe blocks: each node is accessed exactly once.
            if let Some(node_dist) = dist[node] {
                let node_dist: usize = node_dist.into();
                let signed_node_dist: isize = node_dist
                    .try_into()
                    .unwrap_or_else(|_| panic!("Cannot convert {} to isize", node_dist));
                unsafe {
                    *total_distance.get_mut_unsafe(node) += node_dist;
                }

                if lower_bound_eccentricities[node].read()
                    != upper_bound_eccentricities[node].read()
                {
                    let old_lower = lower_bound_eccentricities[node].read();
                    let current_lower =
                        std::cmp::max(max_dist - signed_node_dist, signed_node_dist);
                    let new_lower = std::cmp::max(old_lower, current_lower as usize);
                    unsafe {
                        lower_bound_eccentricities.write_once(node, new_lower);
                    }

                    let old_upper = upper_bound_eccentricities[node].read();
                    let current_upper = if first_branch[node] {
                        std::cmp::max(
                            max_dist - 2 - 2 * start_len + signed_node_dist,
                            signed_node_dist
                                + std::cmp::max(0, ecc_not_first_branch - 2 * start_len),
                        )
                    } else if signed_node_dist < start_len {
                        std::cmp::max(signed_node_dist, max_dist - signed_node_dist)
                    } else {
                        std::cmp::max(max_dist - 2 * start_len + signed_node_dist, max_dist)
                    };
                    let new_upper = std::cmp::min(old_upper, current_upper as usize);
                    unsafe {
                        upper_bound_eccentricities.write_once(node, new_upper);
                    }

                    if lower_bound_eccentricities[node].read()
                        == upper_bound_eccentricities[node].read()
                    {
                        let ecc = lower_bound_eccentricities[node].read();
                        let mut update = false;

                        {
                            let diameter_lock = diameter.read().unwrap();
                            if diameter_lock.0 < ecc {
                                update = true
                            }
                        }

                        if update {
                            let mut diameter_lock = diameter.write().unwrap();
                            if diameter_lock.0 < ecc {
                                diameter_lock.0 = ecc;
                                diameter_lock.1 = node;
                            }
                        }
                        update = false;

                        {
                            let radius_lock = radius.read().unwrap();
                            if radius_lock.0 > ecc {
                                update = true;
                            }
                        }

                        if update {
                            let mut radius_lock = radius.write().unwrap();
                            if radius_lock.0 > ecc {
                                radius_lock.0 = ecc;
                                radius_lock.1 = node;
                            }
                        }
                    }
                }
            }
        });

        let (r, r_v) = radius.into_inner().unwrap();
        let (d, d_v) = diameter.into_inner().unwrap();

        self.radius_upper_bound = r;
        self.radius_vertex = r_v;
        self.diameter_lower_bound = d;
        self.diameter_vertex = d_v;

        self.iterations += 1;

        pl.done();

        Ok(())
    }

    /// Performs `iterations` steps of the SumSweep heuristic starting from vertex `start`.
    ///
    /// The SumSweep heuristic performs BFSes from vertices maximizing the sum of the distance
    /// from the starting vertices of the previous BFSes, and should be considered "*peripheral*".
    /// This way, after few iterations, usually most lower bounds on the eccentricities are tight.
    ///
    /// # Arguments
    /// - `start`: The starting vertex.
    /// - `iterations`: The number of iterations.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn sum_sweep_heuristic(
        &mut self,
        start: usize,
        iterations: usize,
        pl: impl ProgressLog,
    ) -> Result<()> {
        self.step_sum_sweep(Some(start), pl.clone())
            .with_context(|| format!("Cannot perform BFS from {}", start))?;

        for _ in 1..iterations {
            let v = math::filtered_argmax(
                &self.total_distance,
                &self.lower_bound_eccentricities,
                |node, _| self.incomplete_vertex(node),
            );
            self.step_sum_sweep(v, pl.clone())
                .with_context(|| format!("Cannot perform BFS from {:?}", v))?;
        }

        Ok(())
    }

    /// Computes how many nodes are still to be processed, before outputting the result.
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn find_missing_nodes(&mut self, mut pl: impl ProgressLog) -> Result<usize> {
        pl.item_name("nodes");
        pl.display_memory(false);
        pl.expected_updates(Some(self.number_of_nodes));
        pl.start("Computing missing nodes");

        let missing_r = AtomicUsize::new(0);
        let missing_d = AtomicUsize::new(0);
        let missing_all = AtomicUsize::new(0);

        (0..self.number_of_nodes).into_par_iter().for_each(|node| {
            if self.incomplete_vertex(node) {
                missing_all.fetch_add(1, Ordering::Relaxed);
                if self.upper_bound_eccentricities[node] > self.diameter_lower_bound {
                    missing_d.fetch_add(1, Ordering::Relaxed);
                }
                if self.lower_bound_eccentricities[node] < self.radius_upper_bound {
                    missing_r.fetch_add(1, Ordering::Relaxed);
                }
            }
        });

        let iterations =
            NonMaxUsize::new(self.iterations).expect("Iterations should never be usize::MAX");
        let missing_r = missing_r.load(Ordering::Relaxed);
        let missing_d = missing_d.load(Ordering::Relaxed);
        let missing_all = missing_all.load(Ordering::Relaxed);

        if missing_r == 0 && self.radius_iterations.is_none() {
            self.radius_iterations = Some(iterations);
        }
        if missing_d == 0 && self.diameter_iterations.is_none() {
            self.diameter_iterations = Some(iterations);
        }
        if missing_all == 0 {
            self.all_eccentricities_iterations = Some(iterations);
        }

        Ok(match self.output {
            SumSweepOutputLevel::Radius => missing_r,
            SumSweepOutputLevel::Diameter => missing_d,
            SumSweepOutputLevel::RadiusDiameter => missing_r + missing_d,
            _ => missing_all,
        })
    }

    /// Computes diameter, radius, and/or all eccentricities.
    ///
    /// Results can be accessed by methods [`Self::radius`], [`Self::diameter`], [`Self::radial_vertex`],
    /// [`Self::diametral_vertex`], [`Self::eccentricity`].
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    pub fn compute(&mut self, mut pl: impl ProgressLog) -> Result<()> {
        if self.number_of_nodes == 0 {
            return Ok(());
        }
        pl.start("Computing SumSweep...");

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

        self.sum_sweep_heuristic(max_outdegree_vertex.load(Ordering::Relaxed), 3, pl.clone())
            .with_context(|| "Could not perform first 3 iterations of SumSweep heuristic.")?;

        let mut points = [self.graph.num_nodes() as f64; 3];
        let mut missing_nodes = self
            .find_missing_nodes(pl.clone())
            .with_context(|| "Cannot compute missing nodes")?;
        let mut old_missing_nodes;

        pl.info(format_args!(
            "Missing nodes: {} out of {}",
            missing_nodes, self.number_of_nodes
        ));

        while missing_nodes > 0 {
            let step_to_perform =
                math::argmax(&points).with_context(|| "Could not find step to perform")?;

            match step_to_perform {
                0 => {
                    pl.info(format_args!(
                        "Performing a BFS from a vertex maximizing the upper bound."
                    ));
                    let v = math::filtered_argmax(
                        &self.upper_bound_eccentricities,
                        &self.total_distance,
                        |node, _| self.incomplete_vertex(node),
                    );
                    self.step_sum_sweep(v, pl.clone())
                        .with_context(|| format!("Could not perform visit from {:?}", v))?
                }
                1 => {
                    pl.info(format_args!(
                        "Performing a BFS from a vertex minimizing the lower bound."
                    ));
                    let v = math::filtered_argmax(
                        &self.lower_bound_eccentricities,
                        &self.total_distance,
                        |node, _| self.incomplete_vertex(node),
                    );
                    self.step_sum_sweep(v, pl.clone())
                        .with_context(|| format!("Could not perform visit from {:?}", v))?
                }
                2 => {
                    pl.info(format_args!(
                        "Performing a BFS from a vertex maximizing the distance sum."
                    ));
                    let v = math::filtered_argmax(
                        &self.total_distance,
                        &self.upper_bound_eccentricities,
                        |node, _| self.incomplete_vertex(node),
                    );
                    self.step_sum_sweep(v, pl.clone())
                        .with_context(|| format!("Could not perform visit from {:?}", v))?
                }
                3.. => panic!(),
            }

            old_missing_nodes = missing_nodes;
            missing_nodes = self
                .find_missing_nodes(pl.clone())
                .with_context(|| "Could not compute missing nodes")?;
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
                missing_nodes, self.number_of_nodes
            ));
        }

        if self.output == SumSweepOutputLevel::Radius
            || self.output == SumSweepOutputLevel::RadiusDiameter
        {
            pl.info(format_args!(
                "Radius: {} ({} iterations).",
                self.radius_upper_bound,
                self.radius_iterations
                    .expect("radius iterations should not be None")
            ));
        }
        if self.output == SumSweepOutputLevel::Diameter
            || self.output == SumSweepOutputLevel::RadiusDiameter
        {
            pl.info(format_args!(
                "Diameter: {} ({} iterations).",
                self.diameter_lower_bound,
                self.diameter_iterations
                    .expect("radius iterations should not be None"),
            ));
        }
        pl.done();

        Ok(())
    }
}
