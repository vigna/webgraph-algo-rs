use anyhow::Result;
use dsi_progress_logger::prelude::*;
use sux::bit_vec;
use webgraph::graphs::random::ErdosRenyi;
use webgraph::prelude::BvGraph;
use webgraph::traits::RandomAccessGraph;
use webgraph::transform;
use webgraph::{graphs::vec_graph::VecGraph, labels::Left, traits::SequentialLabeling};
use webgraph_algo::algo::scc::*;

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

macro_rules! test_scc_algo {
    ($scc:ident, $name:ident) => {
        mod $name {
            use super::*;

            #[test]
            fn test_buckets() -> Result<()> {
                let graph = Left(VecGraph::from_arc_list([
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
                ]));

                let mut components =
                    $scc::compute(&graph, no_logging![]);

                assert_eq!(components.component()[3], components.component()[4]);

                let mut buckets = bit_vec![false; graph.num_nodes()];
                buckets.set(0, true);
                buckets.set(3, true);
                buckets.set(4, true);

                components.sort_by_size();
                let sizes = components.compute_sizes();

                assert_eq!(sizes, vec![2, 2, 1, 1, 1, 1, 1]);

                Ok(())
            }

            #[test]
            fn test_buckets_2() -> Result<()> {
                let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3)]));

                let mut components =
                    $scc::compute(&graph, no_logging![]);

                components.sort_by_size();
                let sizes = components.compute_sizes();

                assert_eq!(sizes, vec![3, 1]);

                Ok(())
            }

            #[test]
            fn test_cycle() -> Result<()> {
                let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 3), (3, 0)]));

                let mut components =
                    $scc::compute(&graph, no_logging![]);

                components.sort_by_size();
                let sizes = components.compute_sizes();

                assert_eq!(sizes, vec![4]);

                Ok(())
            }

            #[test]
            fn test_complete_graph() -> Result<()> {
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

                let mut components =
                    $scc::compute(&graph, no_logging![]);
                components.sort_by_size();

                for i in 0..5 {
                    assert_eq!(components.component()[i], 0);
                }
                assert_eq!(components.compute_sizes(), vec![5]);

                Ok(())
            }

            #[test]
            fn test_tree() -> Result<()> {
                let graph = Left(VecGraph::from_arc_list([(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)]));
                let mut components =
                    $scc::compute(&graph, no_logging![]);
                components.sort_by_size();

                assert_eq!(components.num_components(), 7);

                Ok(())
            }
        }
    };
}

test_scc_algo!(TarjanStronglyConnectedComponents, tarjan);
//test_scc_algo!(KKStronglyConnectedComponents, kk);

#[test]
fn test_large() -> Result<()> {
    let basename = "tests/graphs/cnr-2000";

    let graph = BvGraph::with_basename(basename).load()?;
    let transpose = BvGraph::with_basename(basename.to_string() + "-t").load()?;

    let kosaraju = Kosaraju::compute_with_t(&graph, &transpose, no_logging![]);
    let tarjan = TarjanStronglyConnectedComponents::compute(&graph, no_logging![]);

    assert_eq!(kosaraju.num_components(), 100977);
    assert_eq!(tarjan.num_components(), 100977);

    Ok(())
}

#[test]
fn test_er() -> Result<()> {
    for n in (10..=100).step_by(10) {
        for d in 1..10 {
            let graph = Left(VecGraph::from_lender(
                ErdosRenyi::new(n, (d as f64) / 10.0, 0).iter(),
            ));

            let transpose = Left(VecGraph::from_lender(
                transform::transpose(&graph, 10000)?.iter(),
            ));
            let kosaraju = Kosaraju::compute_with_t(&graph, &transpose, no_logging![]);
            let tarjan = TarjanStronglyConnectedComponents::compute(&graph, no_logging![]);

            assert_eq!(kosaraju.num_components(), tarjan.num_components());
        }
    }
    Ok(())
}
