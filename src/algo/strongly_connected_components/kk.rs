use super::traits::StronglyConnectedComponents;
use crate::algo::{
    top_sort,
    visits::{dfv::*, SeqVisit},
};
use common_traits::Integer;
use dsi_progress_logger::ProgressLog;
use sux::bits::BitVec;
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

/// Implementation of KK's algorithm to compute the strongly connected components
/// on a graph.
pub struct KKStronglyConnectedComponents {
    n_of_components: usize,
    component: Vec<usize>,
    buckets: Option<BitVec>,
}

impl StronglyConnectedComponents for KKStronglyConnectedComponents {
    fn number_of_components(&self) -> usize {
        self.n_of_components
    }

    fn component(&self) -> &[usize] {
        self.component.as_ref()
    }

    fn component_mut(&mut self) -> &mut [usize] {
        self.component.as_mut()
    }

    fn buckets(&self) -> Option<&BitVec> {
        match &self.buckets {
            Some(b) => Some(b),
            None => None,
        }
    }

    fn compute(
        graph: impl RandomAccessGraph,
        compute_buckets: bool,
        pl: &mut impl ProgressLog,
    ) -> Self {
        let mut visit = KK::new(graph, compute_buckets);

        visit.run(pl);

        KKStronglyConnectedComponents {
            buckets: visit.buckets,
            component: visit.components,
            n_of_components: visit.number_of_components,
        }
    }
}

struct KK<G: RandomAccessGraph> {
    graph: G,
    pub components: Vec<usize>,
    pub buckets: Option<BitVec>,
    pub number_of_components: usize,
}

impl<G: RandomAccessGraph> KK<G> {
    fn new(graph: G, compute_buckets: bool) -> KK<G> {
        let num_nodes = graph.num_nodes();
        KK {
            graph,
            buckets: if compute_buckets {
                Some(BitVec::new(num_nodes))
            } else {
                None
            },
            number_of_components: 0,
            components: vec![0; num_nodes],
        }
    }

    fn run(&mut self, pl: &mut impl ProgressLog) {
        let num_nodes = self.graph.num_nodes();

        pl.item_name("node");
        pl.expected_updates(Some(num_nodes));
        pl.start("Computing strongly connected components");

        let top_sort = top_sort::run(&self.graph, pl);
        dbg!(&top_sort);
        let mut visit = SingleThreadedDepthFirstVisit::<TwoState, std::convert::Infallible, _>::new(
            &self.graph,
        );

        let mut curr_comp = 0.wrapping_sub(1);
        let mut buckets = self.buckets.is_some();
        let mut component = Vec::with_capacity(16);

        for &root in top_sort.iter().rev() {
            eprintln!("Visiting from {}", root);
            visit
                .visit_from_node(
                    root,
                    |&Args {
                         node,
                         pred,
                         root: _root,
                         depth: _depth,
                         event,
                     }| {
                        match event {
                            Event::Unknown => {
                                // TODO: debatable, we should be able to do it
                                // just when necessary
                                if node == pred {
                                    // New root, increase component index
                                    curr_comp = curr_comp.wrapping_add(1);
                                }
                                self.components[node] = curr_comp;
                                if buckets {
                                    component.push(node);
                                }
                            }
                            Event::Known(_b) => {
                                if self.components[node] != curr_comp {
                                    eprintln!(
                                        "Found known node {node} of component {}",
                                        self.components[node]
                                    );
                                    buckets = false;
                                }
                            }
                            _ => {}
                        }

                        Ok(())
                    },
                    |_| true,
                    pl,
                )
                .unwrap_infallible();

            if buckets {
                // SAFETY: if buckets is true, self.buckets.is_some() is true.
                let buckets = self.buckets.as_mut().unwrap();
                for &node in component.iter() {
                    buckets.set(node, true);
                }
            }

            component.clear();
        }

        pl.done();
        self.number_of_components = curr_comp + 1;
    }
}
