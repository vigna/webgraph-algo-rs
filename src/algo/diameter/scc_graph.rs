use crate::{
    prelude::StronglyConnectedComponents,
    utils::{closure_vec, MmapSlice, TempMmapOptions},
};
use anyhow::{Context, Result};
use dsi_progress_logger::ProgressLog;
use mmap_rs::MmapFlags;
use nonmax::NonMaxUsize;
use parallel_frontier::prelude::Frontier;
use rayon::prelude::*;
use std::{marker::PhantomData, sync::Mutex};
use webgraph::traits::RandomAccessGraph;

#[derive(Clone, Debug)]
pub struct SccGraphConnection {
    /// The component this connection is connected to
    pub target: usize,
    /// The start node of the connection
    pub start: usize,
    /// The enc node of the connection
    pub end: usize,
}

pub struct SccGraph<G: RandomAccessGraph + Sync, C: StronglyConnectedComponents<G>> {
    /// Slice of offsets where the `i`-th offset is how many elements to skip in [`Self::data`]
    /// in order to reach the first element relative to component `i`.
    segments_offset: MmapSlice<usize>,
    data: MmapSlice<SccGraphConnection>,
    _phantom_graph: PhantomData<G>,
    _phantom_component: PhantomData<C>,
}

impl<G: RandomAccessGraph + Sync, C: StronglyConnectedComponents<G>> SccGraph<G, C> {
    /// Creates a strongly connected components graph from provided graphs and strongly connected
    /// components.
    ///
    /// # Arguments
    /// - `graph`: An immutable reference to the graph.
    /// - `reversed_graph`: An immutable reference to `graph` transposed.
    /// - `scc`: An immutable reference to a [`StronglyConnectedComponents`] instance.
    /// - `options`: the options for the [`crate::utils::mmap_slice::MmapSlice`].
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    pub fn new(
        graph: &G,
        reversed_graph: &G,
        scc: &C,
        options: TempMmapOptions,
        mut pl: impl ProgressLog,
    ) -> Result<Self> {
        pl.display_memory(false);
        pl.expected_updates(None);
        pl.start("Computing strongly connected components graph...");

        let (vec_lengths, vec_connections) =
            Self::find_edges_through_scc(graph, reversed_graph, scc, pl.clone()).with_context(
                || "Cannot create vector based strongly connected components graph",
            )?;

        let mut flags = MmapFlags::empty();
        flags.set(MmapFlags::SHARED, true);
        flags.set(MmapFlags::RANDOM_ACCESS, true);

        pl.info(format_args!("Memory mapping segment lengths..."));

        let mmap_lengths = MmapSlice::from_vec(vec_lengths, options.clone())
            .with_context(|| "Cannot mmap segment lengths")?;

        pl.info(format_args!("Segment lengths successfully memory mapped"));
        pl.info(format_args!("Memory mapping connections..."));

        let mmap_connections = MmapSlice::from_vec(vec_connections, options.clone())
            .with_context(|| "Cannot mmap connections")?;

        pl.info(format_args!("Connections successfully memory mapped"));
        pl.done();

        Ok(Self {
            segments_offset: mmap_lengths,
            data: mmap_connections,
            _phantom_graph: PhantomData,
            _phantom_component: PhantomData,
        })
    }

    /// The children of the passed strongly connected component.
    ///
    /// # Arguments
    /// - `component`: the component.
    ///
    /// # Panics
    /// Panics if a non existant component index is passed.
    pub fn children(&self, component: usize) -> &[SccGraphConnection] {
        if component >= self.segments_offset.len() {
            panic!(
                "{}",
                format!(
                    "Requested component {}. Graph contains {} components",
                    component,
                    self.segments_offset.len()
                )
            );
        }
        let offset = self.segments_offset[component];
        if component + 1 >= self.segments_offset.len() {
            &self.data[offset..]
        } else {
            &self.data[offset..self.segments_offset[component + 1]]
        }
    }

    /// For each edge in the DAG of strongly connected components, finds a corresponding edge
    /// in the graph. This edge is used in the [`Self::all_cc_upper_bound`] method.
    ///
    /// # Arguments
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn find_edges_through_scc(
        graph: &G,
        reversed_graph: &G,
        scc: &C,
        mut pl: impl ProgressLog,
    ) -> Result<(Vec<usize>, Vec<SccGraphConnection>)> {
        pl.item_name("strongly connected components");
        pl.display_memory(false);
        pl.expected_updates(Some(scc.number_of_components()));
        pl.start("Computing vec-based strongly connected components graph");

        let number_of_scc = scc.number_of_components();
        let node_components = scc.component();
        let mut child_components = Frontier::new();
        let mut vertices_in_scc = vec![Vec::new(); number_of_scc];

        let mut scc_graph = vec![Vec::new(); number_of_scc];
        let mut start_bridges = vec![Vec::new(); number_of_scc];
        let mut end_bridges = vec![Vec::new(); number_of_scc];

        for (vertex, &component) in node_components.iter().enumerate() {
            vertices_in_scc[component].push(vertex);
        }

        {
            let mut best_start: Vec<Option<NonMaxUsize>> = vec![None; number_of_scc];
            let best_end: Vec<Option<NonMaxUsize>> = vec![None; number_of_scc];
            let locks = closure_vec(|| Mutex::new(()), number_of_scc);

            for (c, component) in vertices_in_scc.into_iter().enumerate() {
                component.into_par_iter().for_each(|v| {
                    let best_start_ptr = best_start.as_ptr() as *mut Option<NonMaxUsize>;
                    let best_end_ptr = best_end.as_ptr() as *mut Option<NonMaxUsize>;

                    for succ in graph.successors(v) {
                        let succ_component = node_components[succ];
                        if c != succ_component {
                            let mut updated = false;
                            if best_start[succ_component].is_none() {
                                let _l = locks[succ_component].lock().unwrap();
                                if best_start[succ_component].is_none() {
                                    // Safety: lock and best_end is updated before best_start
                                    unsafe {
                                        *best_end_ptr.add(succ_component) = Some(
                                            NonMaxUsize::new(succ)
                                                .expect("node index should never be usize::MAX"),
                                        );
                                        *best_start_ptr.add(succ_component) = Some(
                                            NonMaxUsize::new(v)
                                                .expect("node index should never be usize::MAX"),
                                        );
                                    }
                                    drop(_l);
                                    child_components.push(succ_component);
                                    updated = true;
                                }
                            }
                            if updated {
                                continue;
                            }

                            let current_value = graph.outdegree(v) + reversed_graph.outdegree(succ);

                            // This if could use incompletly changed pairs of start-end, but it does not influence correctness
                            // as it is only used as a preliminary filter to reduce lock access (at worst the computed best
                            // is < than the actual value, but after lock acquisition this gets fixed with the seconf if).
                            if current_value
                                > graph.outdegree(best_end[succ_component].unwrap().into())
                                    + reversed_graph
                                        .outdegree(best_start[succ_component].unwrap().into())
                            {
                                let _l = locks[succ_component].lock().unwrap();
                                if current_value
                                    > graph.outdegree(best_end[succ_component].unwrap().into())
                                        + reversed_graph
                                            .outdegree(best_start[succ_component].unwrap().into())
                                {
                                    // Safety: lock
                                    unsafe {
                                        *best_end_ptr.add(succ_component) = Some(
                                            NonMaxUsize::new(succ)
                                                .expect("node index should never be usize::MAX"),
                                        );
                                        *best_start_ptr.add(succ_component) = Some(
                                            NonMaxUsize::new(v)
                                                .expect("node index should never be usize::MAX"),
                                        );
                                    }
                                }
                            }
                        }
                    }
                });

                let number_of_children = child_components.len();
                let mut scc_vec = Vec::with_capacity(number_of_children);
                let mut start_vec = Vec::with_capacity(number_of_children);
                let mut end_vec = Vec::with_capacity(number_of_children);
                for &child in child_components.iter() {
                    scc_vec.push(child);
                    start_vec.push(best_start[child].unwrap().into());
                    end_vec.push(best_end[child].unwrap().into());
                    best_start[c] = None;
                }
                scc_graph[c] = scc_vec;
                start_bridges[c] = start_vec;
                end_bridges[c] = end_vec;
                child_components.clear();
                pl.light_update();
            }
        }

        pl.done();

        pl.item_name("connections");
        pl.expected_updates(Some(scc_graph.par_iter().map(|v| v.len()).sum()));
        pl.start("Creating connections slice");

        let mut lengths = Vec::new();
        let mut connections = Vec::new();
        let mut offset = 0;

        for ((children, starts), ends) in scc_graph
            .into_iter()
            .zip(start_bridges.into_iter())
            .zip(end_bridges.into_iter())
        {
            lengths.push(offset);
            for ((child, start), end) in children
                .into_iter()
                .zip(starts.into_iter())
                .zip(ends.into_iter())
            {
                connections.push(SccGraphConnection {
                    target: child,
                    start,
                    end,
                });
                offset += 1;
                pl.light_update();
            }
        }

        pl.done();

        Ok((lengths, connections))
    }
}
