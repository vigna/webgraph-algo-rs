use std::marker::PhantomData;

use super::traits::StronglyConnectedComponents;
use dsi_progress_logger::ProgressLog;
use rayon::prelude::*;
use webgraph::traits::RandomAccessGraph;

pub struct TarjanStronglyConnectedComponents<G: RandomAccessGraph> {
    n_of_components: usize,
    component: Vec<isize>,
    buckets: Option<Vec<bool>>,
    _phantom: PhantomData<G>,
}

impl<G: RandomAccessGraph> StronglyConnectedComponents<G> for TarjanStronglyConnectedComponents<G> {
    fn number_of_components(&self) -> usize {
        self.n_of_components
    }

    fn component(&self) -> &[isize] {
        &self.component
    }

    fn component_mut(&mut self) -> &mut [isize] {
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
            component: visit.status,
            n_of_components: visit.number_of_components,
            _phantom: PhantomData,
        }
    }
}

struct Visit<'a, G: RandomAccessGraph> {
    graph: &'a G,
    number_of_nodes: usize,
    /// For non-visited nodes, 0. For visited non emitted nodes the visit time. For emitted node
    /// *-c-1* where *c* is the component number.
    pub status: Vec<isize>,
    pub buckets: Option<Vec<bool>>,
    component_stack: Vec<usize>,
    /// The first-visit clock (incremented at each visited node).
    clock: isize,
    pub number_of_components: usize,
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
            clock: 0,
            number_of_components: 0,
            number_of_nodes: graph.num_nodes(),
            component_stack: vec![0; graph.num_nodes()],
            status: vec![0; graph.num_nodes()],
        }
    }

    fn run(&mut self, pl: &mut impl ProgressLog) {
        pl.item_name("nodes");
        pl.expected_updates(Some(self.number_of_nodes));
        pl.start("Computing strongly connected components");

        for i in 0..self.number_of_nodes {
            if self.status[i] == 0 {
                self.visit(i, pl);
            }
        }

        pl.done();

        self.status.par_iter_mut().for_each(|s| *s = -(*s) - 1);

        if let Some(b) = self.buckets.as_mut() {
            b.par_iter_mut().for_each(|node| *node = !*node);
        }
    }

    fn visit(&mut self, start_node: usize, pl: &mut impl ProgressLog) {
        let mut older_node_found = Vec::new();
        let mut node_stack = Vec::new();
        let mut successors_stack = Vec::new();

        self.clock += 1;
        self.status[start_node] = self.clock;
        self.component_stack.push(start_node);
        node_stack.push(start_node);
        successors_stack.push(start_node);
        older_node_found.push(false);
        if let Some(b) = self.buckets.as_mut() {
            if self.graph.outdegree(start_node) == 0 {
                b[start_node] = true;
            }
        }

        'main: while !node_stack.is_empty() {
            let current_node = node_stack[node_stack.len() - 1];
            let successors = self
                .graph
                .successors(successors_stack[successors_stack.len() - 1]);

            for succ in successors {
                let successor_status = self.status[succ];
                if successor_status == 0 {
                    self.clock += 1;
                    self.status[succ] = self.clock;
                    node_stack.push(succ);
                    self.component_stack.push(succ);
                    successors_stack.push(succ);
                    older_node_found.push(false);
                    if let Some(b) = self.buckets.as_mut() {
                        if self.graph.outdegree(succ) == 0 {
                            b[succ] = true;
                        }
                    }
                    continue 'main;
                } else if successor_status > 0 {
                    if successor_status < self.status[current_node] {
                        self.status[current_node] = successor_status;
                        older_node_found.pop();
                        older_node_found.push(true);
                    }
                } else if let Some(b) = self.buckets.as_mut() {
                    b[current_node] = true;
                }
            }

            node_stack.pop();
            successors_stack.pop();
            pl.light_update();

            if older_node_found.pop().unwrap_or(false) {
                let parent_node = node_stack[node_stack.len() - 1];
                let current_node_status = self.status[current_node];
                if current_node_status > self.status[parent_node] {
                    self.status[parent_node] = current_node_status;
                    older_node_found.pop();
                    older_node_found.push(true);
                }

                if let Some(b) = self.buckets.as_mut() {
                    if b[current_node] {
                        b[parent_node] = true;
                    }
                }
            } else {
                if let Some(b) = self.buckets.as_mut() {
                    if !node_stack.is_empty() {
                        b[node_stack[node_stack.len() - 1]] = true;
                    }
                }
                let not_a_bucket = match &self.buckets {
                    Some(b) => b[current_node],
                    None => false,
                };
                self.number_of_components += 1;
                let mut z;
                loop {
                    z = self.component_stack.pop().unwrap();
                    self.status[z] = -(self.number_of_components as isize);
                    if not_a_bucket {
                        let b = self.buckets.as_mut().unwrap();
                        b[z] = true;
                    }
                    if z == current_node {
                        break;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use dsi_progress_logger::ProgressLogger;
    use webgraph::{graphs::vec_graph::VecGraph, labels::Left, traits::SequentialLabeling};

    #[test]
    fn test_buckets() {
        let arcs = vec![
            (0, 0),
            (1, 0),
            (1, 2),
            (2, 1),
            (2, 3),
            (2, 4),
            (2, 5),
            (3, 4),
            (4, 3),
            (5, 5),
            (5, 6),
            (5, 7),
            (5, 8),
            (6, 7),
            (8, 7),
        ];
        let mut g = VecGraph::new();
        for i in 0..9 {
            g.add_node(i);
        }
        for arc in arcs {
            g.add_arc(arc.0, arc.1);
        }
        let graph = Left(g);

        let mut components = TarjanStronglyConnectedComponents::compute(
            &graph,
            true,
            Option::<ProgressLogger>::None,
        );

        let mut buckets = vec![false; graph.num_nodes()];
        buckets[0] = true;
        buckets[3] = true;
        buckets[4] = true;
        assert_eq!(buckets, components.buckets.clone().unwrap());

        components.sort_by_size();
        let sizes = components.compute_sizes();

        assert_eq!(vec![2, 2, 1, 1, 1, 1, 1], sizes);
    }

    #[test]
    fn test_buckets_2() {
        let arcs = vec![(0, 1), (1, 2), (2, 0), (1, 3), (3, 3)];
        let mut g = VecGraph::new();
        for i in 0..4 {
            g.add_node(i);
        }
        for arc in arcs {
            g.add_arc(arc.0, arc.1);
        }
        let graph = Left(g);

        let mut components = TarjanStronglyConnectedComponents::compute(
            &graph,
            true,
            Option::<ProgressLogger>::None,
        );

        let mut buckets = vec![false; graph.num_nodes()];
        buckets[3] = true;
        assert_eq!(buckets, components.buckets.clone().unwrap());

        components.sort_by_size();
        let sizes = components.compute_sizes();

        assert_eq!(vec![3, 1], sizes);
    }

    #[test]
    fn test_complete_graph() {
        let mut g = VecGraph::new();
        for i in 0..5 {
            g.add_node(i);
        }
        for i in 0..5 {
            for j in 0..5 {
                if i != j {
                    g.add_arc(i, j);
                }
            }
        }

        let graph = Left(g);

        let mut components = TarjanStronglyConnectedComponents::compute(
            &graph,
            true,
            Option::<ProgressLogger>::None,
        );
        components.sort_by_size();

        assert_eq!(
            vec![true; graph.num_nodes()],
            components.buckets.clone().unwrap()
        );

        for i in 0..5 {
            assert_eq!(0, components.component()[i]);
        }
        assert_eq!(vec![5], components.compute_sizes());
    }

    #[test]
    fn test_tree() {
        let arcs = vec![(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)];
        let mut g = VecGraph::new();
        for i in 0..7 {
            g.add_node(i);
        }
        for arc in arcs {
            g.add_arc(arc.0, arc.1);
        }

        let graph = Left(g);

        let mut components = TarjanStronglyConnectedComponents::compute(
            &graph,
            true,
            Option::<ProgressLogger>::None,
        );
        components.sort_by_size();

        assert_eq!(
            vec![false; graph.num_nodes()],
            components.buckets.clone().unwrap()
        );

        assert_eq!(7, components.number_of_components());
    }
}
