use anyhow::Result;
use dsi_progress_logger::prelude::*;
use sux::bit_vec;
use webgraph::graphs::random::ErdosRenyi;
use webgraph::prelude::BvGraph;
use webgraph::transform;
use webgraph::{graphs::vec_graph::VecGraph, labels::Left, traits::SequentialLabeling};
use webgraph_algo::algo::scc::*;
use webgraph_algo::prelude::*;

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
                let transpose = Left(VecGraph::from_lender(transform::transpose(&graph, 10000)?.iter(),));

                let mut components =
                    $scc::compute(&graph, &transpose, no_logging![]);

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
                let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0), (1, 3), (3, 3)]));
                let transpose = Left(VecGraph::from_lender(transform::transpose(&graph, 10000)?.iter(),));

                let mut components =
                    $scc::compute(&graph, &transpose, no_logging![]);

                components.sort_by_size();
                let sizes = components.compute_sizes();

                assert_eq!(sizes, vec![3, 1]);

                Ok(())
            }

            #[test]
            fn test_cycle() -> Result<()> {
                let graph = Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 3), (3, 0)]));
                let transpose = Left(VecGraph::from_lender(transform::transpose(&graph, 10000)?.iter(),));

                let mut components =
                    $scc::compute(&graph, &transpose, no_logging![]);

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
                let transpose = Left(VecGraph::from_lender(transform::transpose(&graph, 10000)?.iter(),));

                let mut components =
                    $scc::compute(&graph, &transpose, no_logging![]);
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
                let transpose = Left(VecGraph::from_lender(transform::transpose(&graph, 10000)?.iter(),));
                let mut components =
                    $scc::compute(&graph,&transpose, no_logging![]);
                components.sort_by_size();

                assert_eq!(components.number_of_components(), 7);

                Ok(())
            }
        }
    };
}

test_scc_algo!(TarjanStronglyConnectedComponents, tarjan);
test_scc_algo!(Kosaraju, kosaraju);

#[test]
fn test_large() -> Result<()> {
    let basename = "tests/graphs/cnr-2000";

    let graph = BvGraph::with_basename(basename).load()?;
    let transpose = BvGraph::with_basename(basename.to_string() + "-t").load()?;

    let kosaraju = Kosaraju::compute(&graph, &transpose, no_logging![]);
    let tarjan = TarjanStronglyConnectedComponents::compute_no_transpose(&graph, no_logging![]);

    assert_eq!(kosaraju.number_of_components(), 100977);
    assert_eq!(tarjan.number_of_components(), 100977);

    Ok(())
}

#[test]
fn test_er() -> Result<()> {
    for n in (1..100).step_by(10) {
        for d in 1..10 {
            let graph = Left(VecGraph::from_lender(
                ErdosRenyi::new(n, (d as f64) / 10.0, 0).iter(),
            ));

            let transpose = Left(VecGraph::from_lender(
                transform::transpose(&graph, 10000)?.iter(),
            ));
            let kosaraju = Kosaraju::compute(&graph, &transpose, no_logging![]);
            let tarjan =
                TarjanStronglyConnectedComponents::compute_no_transpose(&graph, no_logging![]);

            assert_eq!(
                kosaraju.number_of_components(),
                tarjan.number_of_components()
            );
        }
    }
    Ok(())
}
