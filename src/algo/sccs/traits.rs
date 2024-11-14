use dsi_progress_logger::ProgressLog;
use rayon::prelude::*;
use webgraph::{algo::llp, traits::RandomAccessGraph};

/// The strongly connected components on a graph.
pub trait StronglyConnectedComponents {
    /// The number of strongly connected components.
    fn num_components(&self) -> usize;

    /// The component index of each node.
    fn component(&self) -> &[usize];

    /// The mutable reference to the component index of each node.
    #[doc(hidden)]
    fn component_mut(&mut self) -> &mut [usize];

    /// Computes the strongly connected components of a given graph using also
    /// its transpose.
    ///
    /// # Arguments:
    /// * `graph`: the graph whose strongly connected components are to be computed.
    /// * `transpose`: the transpose of `graph`.
    /// * `compute_buckets`: if `true`, buckets will be computed.
    /// * `pl`: A progress logger.
    #[allow(unused_variables)]
    fn compute_with_t(
        graph: impl RandomAccessGraph,
        transpose: impl RandomAccessGraph,
        pl: &mut impl ProgressLog,
    ) -> Self;

    /// Returns the size array for this set of strongly connected components.
    fn compute_sizes(&self) -> Vec<usize> {
        let mut sizes = vec![0; self.num_components()];
        for &node_component in self.component() {
            sizes[node_component] += 1;
        }
        sizes
    }

    /// Renumbers by decreasing size the components of this set.
    ///
    /// After a call to this method, the internal state of this struct are permuted so that the sizes of
    /// strongly connected components are decreasing in the component index.
    fn sort_by_size(&mut self) {
        let sizes = self.compute_sizes();
        let mut sort_perm = Vec::from_iter(0..sizes.len());
        sort_perm.sort_unstable_by(|&x, &y| sizes[y].cmp(&sizes[x]));
        let mut inv_perm = vec![0; sizes.len()];
        llp::invert_permutation(&sort_perm, &mut inv_perm);
        self.component_mut()
            .par_iter_mut()
            .for_each(|node_component| *node_component = inv_perm[*node_component]);
    }
}

pub trait StronglyConnectedComponentsNoT: StronglyConnectedComponents + Sized {
    /// Computes the strongly connected components of a given graph.
    ///
    /// # Arguments:
    /// * `graph`: the graph whose strongly connected components are to be computed.
    /// * `compute_buckets`: if `true`, buckets will be computed.
    /// * `pl`: A progress logger.
    fn compute(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Self;
}

#[cfg(test)]
mod test {
    use super::*;
    use anyhow::Result;
    use webgraph::prelude::BvGraph;
    use webgraph::traits::RandomAccessGraph;

    struct MockStronglyConnectedComponent<G: RandomAccessGraph> {
        component: Vec<usize>,
        num: usize,
        _g: G,
    }

    impl<G: RandomAccessGraph> MockStronglyConnectedComponent<G> {
        fn mock(component: Vec<usize>, num: usize, g: G) -> MockStronglyConnectedComponent<G> {
            MockStronglyConnectedComponent {
                component,
                num,
                _g: g,
            }
        }
    }

    impl<G: RandomAccessGraph> StronglyConnectedComponents for MockStronglyConnectedComponent<G> {
        fn compute_with_t(
            _graph: impl RandomAccessGraph,
            _transpose: impl RandomAccessGraph,
            _pl: &mut impl ProgressLog,
        ) -> Self {
            panic!()
        }
        fn component(&self) -> &[usize] {
            self.component.as_slice()
        }
        fn component_mut(&mut self) -> &mut [usize] {
            self.component.as_mut_slice()
        }
        fn num_components(&self) -> usize {
            self.num
        }
    }

    #[test]
    fn test_compute_sizes() -> Result<()> {
        let mock_component = vec![0, 0, 0, 1, 2, 2, 1, 2, 0, 0];
        let mock_strongly_connected_components = MockStronglyConnectedComponent::mock(
            mock_component,
            3,
            BvGraph::with_basename("tests/graphs/cnr-2000").load()?,
        );

        assert_eq!(
            mock_strongly_connected_components.compute_sizes(),
            vec![5, 2, 3]
        );

        Ok(())
    }

    #[test]
    fn test_sort_by_size() -> Result<()> {
        let mock_component = vec![0, 1, 1, 1, 0, 2];
        let mut mock_strongly_connected_components = MockStronglyConnectedComponent::mock(
            mock_component,
            3,
            BvGraph::with_basename("tests/graphs/cnr-2000").load()?,
        );

        mock_strongly_connected_components.sort_by_size();

        assert_eq!(
            mock_strongly_connected_components.component().to_owned(),
            vec![1, 0, 0, 0, 1, 2]
        );

        Ok(())
    }
}
