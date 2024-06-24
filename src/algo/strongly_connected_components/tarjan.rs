use super::traits::StronglyConnectedComponents;
use crate::{algo::dfv::DFV, prelude::*, utils::MmapSlice};
use anyhow::{Context, Result};
use dsi_progress_logger::ProgressLog;
use nonmax::NonMaxUsize;
use std::marker::PhantomData;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

pub struct TarjanStronglyConnectedComponents<G: RandomAccessGraph> {
    n_of_components: usize,
    component: MmapSlice<usize>,
    buckets: Option<Vec<bool>>,
    _phantom: PhantomData<G>,
}

impl<G: RandomAccessGraph + Sync> StronglyConnectedComponents<G>
    for TarjanStronglyConnectedComponents<G>
{
    fn number_of_components(&self) -> usize {
        self.n_of_components
    }

    fn component(&self) -> &[usize] {
        self.component.as_ref()
    }

    fn component_mut(&mut self) -> &mut [usize] {
        self.component.as_mut()
    }

    fn buckets(&self) -> Option<&[bool]> {
        match &self.buckets {
            Some(b) => Some(b),
            None => None,
        }
    }

    fn compute(
        graph: &G,
        compute_buckets: bool,
        options: TempMmapOptions,
        pl: impl ProgressLog,
    ) -> Result<Self> {
        let mut visit = Visit::new(graph, compute_buckets);

        visit
            .run(pl.clone())
            .with_context(|| "Cannot compute tarjan algorithm")?;

        pl.info(format_args!("Memory mapping components..."));

        let component_mmap = MmapSlice::from_vec(visit.components, options)
            .with_context(|| "Cannot mmap components")?;

        pl.info(format_args!("Components successfully memory mapped"));

        Ok(TarjanStronglyConnectedComponents {
            buckets: visit.buckets,
            component: component_mmap,
            n_of_components: visit.number_of_components,
            _phantom: PhantomData,
        })
    }
}

struct Visit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    pub components: Vec<usize>,
    pub buckets: Option<Vec<bool>>,
    indexes: Vec<Option<NonMaxUsize>>,
    lowlinks: Vec<usize>,
    on_stack: BitVec,
    terminal: Option<BitVec>,
    /// The first-visit clock (incremented at each visited node).
    current_index: usize,
    pub number_of_components: usize,
    stack: Vec<usize>,
}

impl<'a, G: RandomAccessGraph + Sync> Visit<'a, G> {
    fn new(graph: &'a G, compute_buckets: bool) -> Visit<'a, G> {
        Visit {
            graph,
            buckets: if compute_buckets {
                Some(vec![false; graph.num_nodes()])
            } else {
                None
            },
            terminal: if compute_buckets {
                Some(BitVec::with_value(graph.num_nodes(), true))
            } else {
                None
            },
            current_index: 0,
            indexes: vec![None; graph.num_nodes()],
            lowlinks: vec![usize::MAX; graph.num_nodes()],
            on_stack: BitVec::new(graph.num_nodes()),
            number_of_components: 0,
            components: vec![0; graph.num_nodes()],
            stack: Vec::new(),
        }
    }

    fn run(&mut self, mut pl: impl ProgressLog) -> Result<()> {
        let mut visit = DFV::new_sequential(self.graph).build();
        pl.item_name("nodes");
        pl.expected_updates(Some(self.graph.num_nodes()));
        pl.start("Computing strongly connected components");

        for node_to_visit in 0..self.graph.num_nodes() {
            if self.indexes[node_to_visit].is_none() {
                visit
                    .visit_from_node(
                        |node, parent, _, _, event| match event {
                            // Safety: code is sequential: no concurrency and references are not left dangling
                            // a &mut self is requested so compiler should not optimize memory with readonly
                            DepthFirstVisitEvent::Discover => unsafe {
                                self.indexes.write_once(
                                    node,
                                    Some(
                                        NonMaxUsize::new(self.current_index)
                                            .expect("indexes should not exceed usize::MAX"),
                                    ),
                                );
                                self.lowlinks.write_once(node, self.current_index);
                                *self.current_index.as_mut_unsafe() += 1;
                                self.stack.as_mut_unsafe().push(node);
                                self.on_stack.as_mut_unsafe().set(node, true);
                            },
                            DepthFirstVisitEvent::AlreadyVisited => unsafe {
                                if self.on_stack[node] {
                                    self.lowlinks.write_once(
                                        parent,
                                        std::cmp::min(
                                            self.lowlinks[parent],
                                            self.indexes[node].unwrap().into(),
                                        ),
                                    );
                                } else if let Some(t) = self.terminal.as_ref() {
                                    t.as_mut_unsafe().set(parent, false);
                                }
                            },
                            DepthFirstVisitEvent::Emit => unsafe {
                                if self.lowlinks[node] == self.indexes[node].unwrap().into() {
                                    if let Some(b) = self.buckets.as_mut_unsafe() {
                                        let t = self.terminal.as_ref().unwrap().as_mut_unsafe();
                                        let terminal = t[node];
                                        let stack = self.stack.as_mut_unsafe();
                                        while let Some(v) = stack.pop() {
                                            self.components
                                                .write_once(v, self.number_of_components);
                                            self.on_stack.as_mut_unsafe().set(v, false);
                                            t.set(v, false);
                                            if terminal && self.graph.outdegree(v) != 0 {
                                                b[v] = true;
                                            }
                                            if v == node {
                                                break;
                                            }
                                        }
                                    } else {
                                        let stack = self.stack.as_mut_unsafe();
                                        while let Some(v) = stack.pop() {
                                            self.components
                                                .write_once(v, self.number_of_components);
                                            self.on_stack.as_mut_unsafe().set(v, false);
                                            if v == node {
                                                break;
                                            }
                                        }
                                    }
                                    *self.number_of_components.as_mut_unsafe() += 1;
                                }

                                if node != parent {
                                    self.lowlinks.write_once(
                                        parent,
                                        std::cmp::min(self.lowlinks[parent], self.lowlinks[node]),
                                    );
                                    if let Some(t) = self.terminal.as_ref() {
                                        if !t[node] {
                                            t.as_mut_unsafe().set(parent, false);
                                        }
                                    }
                                }
                            },
                        },
                        node_to_visit,
                        &mut pl,
                    )
                    .with_context(|| "Cannot perform depth first visit")?;
            }
        }

        pl.done();

        Ok(())
    }
}
