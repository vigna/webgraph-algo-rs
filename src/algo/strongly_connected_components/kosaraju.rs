use crate::{algo::top_sort, algo::visits::Sequential, prelude::depth_first::*};
use common_traits::Integer;
use dsi_progress_logger::ProgressLog;
use rayon::iter::{IntoParallelRefMutIterator, ParallelIterator};
use unwrap_infallible::UnwrapInfallible;
use webgraph::traits::RandomAccessGraph;

/// Implementation of Kosaraju's algorithm to compute the strongly connected components
/// on a graph.
pub struct Kosaraju {
    n_of_components: usize,
    component: Vec<usize>,
}

impl Kosaraju {
    pub fn number_of_components(&self) -> usize {
        self.n_of_components
    }

    pub fn component(&self) -> &[usize] {
        self.component.as_ref()
    }

    pub fn component_mut(&mut self) -> &mut [usize] {
        self.component.as_mut()
    }
    pub fn compute(
        graph: &impl RandomAccessGraph,
        transpose: &impl RandomAccessGraph,
        pl: &mut impl ProgressLog,
    ) -> Self {
        let top_sort = top_sort::run(graph, pl);
        let mut comp_index = 0.wrapping_sub(1);
        let mut visit = Seq::new(transpose);
        let mut component = vec![0; graph.num_nodes()];

        for &node in &top_sort {
            visit
                .visit(
                    node,
                    |event| {
                        match event {
                            Event::Init { .. } => {
                                comp_index = comp_index.wrapping_add(1);
                            }
                            Event::Previsit { curr, .. } => {
                                component[curr] = comp_index;
                            }
                            _ => (),
                        }
                        Ok(())
                    },
                    pl,
                )
                .unwrap_infallible();
        }
        Kosaraju {
            component,
            n_of_components: comp_index + 1,
        }
    }

    /// Returns the size array for this set of strongly connected components.
    pub fn compute_sizes(&self) -> Vec<usize> {
        let mut sizes = vec![0; self.number_of_components()];
        for &node_component in self.component() {
            sizes[node_component] += 1;
        }
        sizes
    }

    /// Renumbers by decreasing size the components of this set.
    ///
    /// After a call to this method, the internal state of this struct are permuted so that the sizes of
    /// strongly connected components are decreasing in the component index.
    pub fn sort_by_size(&mut self) {
        let sizes = self.compute_sizes();
        let new_order = {
            let mut tmp = Vec::from_iter(0..sizes.len());
            tmp.sort_unstable_by_key(|&element| -(sizes[element] as isize));
            let mut perm = Vec::new();
            for i in 0..sizes.len() {
                let mut new_index = 0;
                while tmp[new_index] != i {
                    new_index += 1;
                }
                perm.push(new_index);
            }
            perm
        };
        self.component_mut()
            .par_iter_mut()
            .for_each(|node_component| *node_component = new_order[*node_component]);
    }
}
