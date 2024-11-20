mod tarjan;
use rayon::iter::{IntoParallelRefMutIterator, ParallelIterator};
pub use tarjan::*;

mod kosaraju;
pub use kosaraju::*;
mod symm_seq;
pub use symm_seq::*;

mod symm_par;
pub use symm_par::*;
use webgraph::algo::llp;

/// The strongly connected components on a graph.
///
/// This trait is implemented by the result of all strongly connected components
/// algorithms. Some algorithms may provide additional information not
/// accessibe through this trait.
pub trait StronglyConnectedComponents {
    /// The number of strongly connected components.
    fn num_components(&self) -> usize;

    /// The component index of each node.
    fn components(&self) -> &[usize];

    /// The mutable reference to the component index of each node.
    #[doc(hidden)]
    fn component_mut(&mut self) -> &mut [usize];

    /// Returns the sizes of all components.
    fn compute_sizes(&self) -> Box<[usize]> {
        let mut sizes = vec![0; self.num_components()];
        for &node_component in self.components() {
            sizes[node_component] += 1;
        }
        sizes.into_boxed_slice()
    }

    /// Renumbers by decreasing size the components of this set.
    ///
    /// After a call to this method, the sizes of strongly connected components
    /// will decreasing in the component index. The method returns the sizes of
    /// the components after the renumbering.
    fn sort_by_size(&mut self) -> Box<[usize]> {
        let mut sizes = self.compute_sizes();
        assert!(sizes.len() == self.num_components());
        let mut sort_perm = Vec::from_iter(0..sizes.len());
        sort_perm.sort_unstable_by(|&x, &y| sizes[y].cmp(&sizes[x]));
        let mut inv_perm = vec![0; sizes.len()];
        llp::invert_permutation(&sort_perm, &mut inv_perm);
        self.component_mut()
            .par_iter_mut()
            .for_each(|node_component| *node_component = inv_perm[*node_component]);
        sizes.sort_by(|&x, &y| y.cmp(&x));
        sizes
    }
}

/// A standard implementation of the `StronglyConnectedComponents` trait.
pub struct BasicSccs {
    num_components: usize,
    components: Box<[usize]>,
}

impl BasicSccs {
    pub fn new(num_components: usize, components: Box<[usize]>) -> Self {
        BasicSccs {
            num_components,
            components,
        }
    }
}

impl StronglyConnectedComponents for BasicSccs {
    fn num_components(&self) -> usize {
        self.num_components
    }

    fn components(&self) -> &[usize] {
        &self.components
    }

    fn component_mut(&mut self) -> &mut [usize] {
        &mut self.components
    }
}
