use super::traits::StronglyConnectedComponents;
use crate::algo::{
    top_sort,
    visits::{dfv::*, SeqVisit},
};
use common_traits::Integer;
use dsi_progress_logger::ProgressLog;
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

/// Implementation of KK's algorithm to compute the strongly connected components
/// on a graph.
pub struct KKStronglyConnectedComponents {
    num_components: usize,
    component: Vec<usize>,
}

impl StronglyConnectedComponents for KKStronglyConnectedComponents {
    fn number_of_components(&self) -> usize {
        self.num_components
    }

    fn component(&self) -> &[usize] {
        self.component.as_ref()
    }

    fn component_mut(&mut self) -> &mut [usize] {
        self.component.as_mut()
    }

    fn compute(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Self {
        let mut visit = KK::new(graph);

        visit.run(pl);

        KKStronglyConnectedComponents {
            component: visit.components,
            num_components: visit.number_of_components,
        }
    }
}

struct KK<G: RandomAccessGraph> {
    graph: G,
    pub components: Vec<usize>,
    pub number_of_components: usize,
}

impl<G: RandomAccessGraph> KK<G> {
    fn new(graph: G) -> KK<G> {
        let num_nodes = graph.num_nodes();
        KK {
            graph,
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
        let mut component = Vec::<usize>::with_capacity(16);

        for &root in top_sort.iter().rev() {
            eprintln!("Visiting from {}", root);
            visit
                .visit_from_node(
                    root,
                    |&Args {
                         curr,
                         pred,
                         root: _root,
                         depth: _depth,
                         event,
                     }| {
                        match event {
                            Event::Previsit => {
                                // TODO: debatable, we should be able to do it
                                // just when necessary
                                if curr == pred {
                                    // New root, increase component index
                                    curr_comp = curr_comp.wrapping_add(1);
                                }
                                self.components[curr] = curr_comp;
                            }
                            Event::Revisit(_b) => {
                                if self.components[curr] != curr_comp {
                                    eprintln!(
                                        "Found known node {curr} of component {}",
                                        self.components[curr]
                                    );
                                }
                            }
                            _ => {}
                        }

                        Ok(())
                    },
                    pl,
                )
                .unwrap_infallible();

            component.clear();
        }

        pl.done();
        self.number_of_components = curr_comp + 1;
    }
}
