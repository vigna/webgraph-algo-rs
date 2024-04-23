use dsi_progress_logger::ProgressLogger;
use webgraph::{graphs::vec_graph::VecGraph, labels::Left, traits::SequentialLabeling};
use webgraph_algo::algo::strongly_connected_components::*;
use webgraph_algo::prelude::*;

macro_rules! test_scc_algo {
    ($scc:ident, $name:ident) => {
        mod $name {
            use super::*;

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

                let mut components = $scc::compute(&graph, true, Option::<ProgressLogger>::None);

                let mut buckets = vec![false; graph.num_nodes()];
                buckets[0] = true;
                buckets[3] = true;
                buckets[4] = true;
                assert_eq!(buckets, components.buckets().clone().unwrap());

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

                let mut components = $scc::compute(&graph, true, Option::<ProgressLogger>::None);

                let mut buckets = vec![false; graph.num_nodes()];
                buckets[3] = true;
                assert_eq!(buckets, components.buckets().clone().unwrap());

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

                let mut components = $scc::compute(&graph, true, Option::<ProgressLogger>::None);
                components.sort_by_size();

                assert_eq!(
                    vec![true; graph.num_nodes()],
                    components.buckets().clone().unwrap()
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

                let mut components = $scc::compute(&graph, true, Option::<ProgressLogger>::None);
                components.sort_by_size();

                assert_eq!(
                    vec![false; graph.num_nodes()],
                    components.buckets().clone().unwrap()
                );

                assert_eq!(7, components.number_of_components());
            }
        }
    };
}

test_scc_algo!(TarjanStronglyConnectedComponents, tarjan);
