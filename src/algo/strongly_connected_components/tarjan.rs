use super::traits::StronglyConnectedComponents;
use dsi_progress_logger::ProgressLog;
use std::marker::PhantomData;
use sux::bits::BitVec;
use webgraph::traits::RandomAccessGraph;

pub struct TarjanStronglyConnectedComponents<G: RandomAccessGraph> {
    n_of_components: usize,
    component: Vec<usize>,
    buckets: Option<Vec<bool>>,
    _phantom: PhantomData<G>,
}

type RecurseNode = (usize, Option<usize>, Option<usize>);

impl<G: RandomAccessGraph> StronglyConnectedComponents<G> for TarjanStronglyConnectedComponents<G> {
    fn number_of_components(&self) -> usize {
        self.n_of_components
    }

    fn component(&self) -> &[usize] {
        &self.component
    }

    fn component_mut(&mut self) -> &mut [usize] {
        &mut self.component
    }

    fn buckets(&self) -> Option<&[bool]> {
        match &self.buckets {
            Some(b) => Some(b),
            None => None,
        }
    }

    fn compute(graph: &G, compute_buckets: bool, mut pl: impl ProgressLog) -> Self {
        let mut visit = Visit::new(graph, compute_buckets);
        visit.run(&mut pl);
        TarjanStronglyConnectedComponents {
            buckets: visit.buckets,
            component: visit.components,
            n_of_components: visit.number_of_components,
            _phantom: PhantomData,
        }
    }
}

struct Visit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    number_of_nodes: usize,
    pub components: Vec<usize>,
    pub buckets: Option<Vec<bool>>,
    indexes: Vec<Option<usize>>,
    lowlinks: Vec<usize>,
    on_stack: BitVec,
    terminal: Option<BitVec>,
    /// The first-visit clock (incremented at each visited node).
    current_index: usize,
    pub number_of_components: usize,
    stack: Vec<usize>,
    iterative_stack: Vec<RecurseNode>,
}

impl<'a, G: RandomAccessGraph> Visit<'a, G> {
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
            number_of_nodes: graph.num_nodes(),
            components: vec![0; graph.num_nodes()],
            stack: Vec::new(),
            iterative_stack: Vec::new(),
        }
    }

    fn run(&mut self, pl: &mut impl ProgressLog) {
        pl.item_name("nodes");
        pl.expected_updates(Some(self.number_of_nodes));
        pl.start("Computing strongly connected components");

        for i in 0..self.number_of_nodes {
            if self.indexes[i].is_none() {
                self.visit(i, pl);
            }
        }

        pl.done();
    }

    fn visit(&mut self, start_node: usize, pl: &mut impl ProgressLog) {
        debug_assert!(self.stack.is_empty());
        debug_assert!(self.iterative_stack.is_empty());
        self.iterative_stack.push((start_node, None, None));

        'recurse: while let Some((v, iter_count, resume)) = self.iterative_stack.pop() {
            if let Some(w) = resume {
                // Finish recurse
                debug_assert!(self.indexes[w].is_some());

                self.lowlinks[v] = std::cmp::min(self.lowlinks[v], self.lowlinks[w]);
                if let Some(t) = self.terminal.as_mut() {
                    if !t[w] {
                        t.set(v, false);
                    }
                }
            } else {
                // Set the depth index for v to the smallest unused index
                debug_assert!(self.lowlinks[v] == usize::MAX);
                debug_assert!(!self.on_stack[v]);
                debug_assert!(!self.stack.contains(&v));
                debug_assert!(self.indexes[v].is_none());

                self.indexes[v] = Some(self.current_index);
                self.lowlinks[v] = self.current_index;
                self.current_index += 1;
                self.stack.push(v);
                self.on_stack.set(v, true);
            }

            let mut count = iter_count.unwrap_or(0);

            for w in self.graph.successors(v).into_iter().skip(count) {
                count += 1;
                if let Some(i) = self.indexes[w] {
                    if self.on_stack[w] {
                        // Successor w is in stack self.stack and hence in the current SCC
                        // If w is not on stack, then (v, w) is an edge pointing to an SCC already found and must be ignored
                        self.lowlinks[v] = std::cmp::min(self.lowlinks[v], i);
                    } else if let Some(t) = self.terminal.as_mut() {
                        t.set(v, false);
                    }
                } else {
                    // Successor w has not yet been visited; recurse on it
                    self.iterative_stack.push((v, Some(count), Some(w)));
                    self.iterative_stack.push((w, None, None));
                    continue 'recurse;
                }
            }

            pl.light_update();

            // If v is a root node, pop the stack and generate an SCC
            if self.lowlinks[v] == self.indexes[v].unwrap() {
                if let Some(b) = self.buckets.as_mut() {
                    let t = self.terminal.as_mut().unwrap();
                    let terminal = t[v];
                    while let Some(node) = self.stack.pop() {
                        self.components[node] = self.number_of_components;
                        self.on_stack.set(node, false);
                        t.set(node, false);
                        if terminal && self.graph.outdegree(node) != 0 {
                            b[node] = true;
                        }
                        if node == v {
                            break;
                        }
                    }
                } else {
                    while let Some(node) = self.stack.pop() {
                        self.components[node] = self.number_of_components;
                        self.on_stack.set(node, false);
                        if node == v {
                            break;
                        }
                    }
                }
                self.number_of_components += 1;
            }
        }
    }
}
