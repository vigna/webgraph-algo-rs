use anyhow::Result;
use dsi_progress_logger::ProgressLogger;
use webgraph::{graphs::vec_graph::VecGraph, labels::Left, traits::SequentialLabeling};
use webgraph_algo::algo::strongly_connected_components::*;
use webgraph_algo::prelude::*;
use webgraph_algo::utils::mmap_slice::TempMmapOptions;

macro_rules! test_scc_algo {
    ($scc:ident, $name:ident) => {
        mod $name {
            use super::*;

            #[test]
            fn test_buckets() -> Result<()> {
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

                let mut components = $scc::compute(
                    &graph,
                    true,
                    TempMmapOptions::None,
                    Option::<ProgressLogger>::None,
                )?;

                assert_eq!(components.component()[3], components.component()[4]);

                let mut buckets = vec![false; graph.num_nodes()];
                buckets[0] = true;
                buckets[3] = true;
                buckets[4] = true;
                assert_eq!(components.buckets().clone().unwrap(), buckets);

                components.sort_by_size();
                let sizes = components.compute_sizes();

                assert_eq!(sizes, vec![2, 2, 1, 1, 1, 1, 1]);

                Ok(())
            }

            #[test]
            fn test_buckets_2() -> Result<()> {
                let arcs = vec![(0, 1), (1, 2), (2, 0), (1, 3), (3, 3)];
                let mut g = VecGraph::new();
                for i in 0..4 {
                    g.add_node(i);
                }
                for arc in arcs {
                    g.add_arc(arc.0, arc.1);
                }
                let graph = Left(g);

                let mut components = $scc::compute(
                    &graph,
                    true,
                    TempMmapOptions::None,
                    Option::<ProgressLogger>::None,
                )?;

                let mut buckets = vec![false; graph.num_nodes()];
                buckets[3] = true;
                assert_eq!(components.buckets().clone().unwrap(), buckets);

                components.sort_by_size();
                let sizes = components.compute_sizes();

                assert_eq!(sizes, vec![3, 1]);

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

                let mut components = $scc::compute(
                    &graph,
                    true,
                    TempMmapOptions::None,
                    Option::<ProgressLogger>::None,
                )?;
                components.sort_by_size();

                assert_eq!(
                    components.buckets().clone().unwrap(),
                    vec![true; graph.num_nodes()]
                );

                for i in 0..5 {
                    assert_eq!(components.component()[i], 0);
                }
                assert_eq!(components.compute_sizes(), vec![5]);

                Ok(())
            }

            #[test]
            fn test_tree() -> Result<()> {
                let arcs = vec![(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)];
                let mut g = VecGraph::new();
                for i in 0..7 {
                    g.add_node(i);
                }
                for arc in arcs {
                    g.add_arc(arc.0, arc.1);
                }

                let graph = Left(g);

                let mut components = $scc::compute(
                    &graph,
                    true,
                    TempMmapOptions::None,
                    Option::<ProgressLogger>::None,
                )?;
                components.sort_by_size();

                assert_eq!(
                    components.buckets().clone().unwrap(),
                    vec![false; graph.num_nodes()]
                );

                assert_eq!(components.number_of_components(), 7);

                Ok(())
            }
        }
    };
}

test_scc_algo!(TarjanStronglyConnectedComponents, tarjan);
