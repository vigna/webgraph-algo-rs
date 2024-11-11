use dsi_progress_logger::ProgressLog;
use rayon::prelude::*;
use webgraph::traits::RandomAccessGraph;

/// The strongly connected components on a graph.
pub trait StronglyConnectedComponents {
    /// The number of strongly connected components.
    fn number_of_components(&self) -> usize;

    /// The component index of each node.
    fn component(&self) -> &[usize];

    /// The mutable reference to the component index of each node.
    fn component_mut(&mut self) -> &mut [usize];

    /// Computes the strongly connected components of a given graph without the transposed
    /// if possible.
    ///
    /// # Arguments:
    /// * `graph`: the graph whose strongly connected components are to be computed.
    /// * `compute_buckets`: if `true`, buckets will be computed.
    /// * `pl`: A progress logger.
    fn compute_no_transpose(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> Self;

    /// Computes the strongly connected components of a given graph with the transposed.
    ///
    /// # Arguments:
    /// * `graph`: the graph whose strongly connected components are to be computed.
    /// * `transposed`: the tansposed of `graph`.
    /// * `compute_buckets`: if `true`, buckets will be computed.
    /// * `pl`: A progress logger.
    #[inline(always)]
    #[allow(unused_variables)]
    fn compute(
        graph: impl RandomAccessGraph,
        transpose: impl RandomAccessGraph,
        pl: &mut impl ProgressLog,
    ) -> Self
    where
        Self: Sized,
    {
        Self::compute_no_transpose(graph, pl)
    }

    /// Returns the size array for this set of strongly connected components.
    fn compute_sizes(&self) -> Vec<usize> {
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
    fn sort_by_size(&mut self) {
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
        fn compute_no_transpose(
            _graph: impl RandomAccessGraph,
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
        fn number_of_components(&self) -> usize {
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
