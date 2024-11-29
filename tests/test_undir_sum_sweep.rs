use anyhow::Result;
use dsi_progress_logger::no_logging;
use std::ops::ControlFlow::Continue;
use webgraph::graphs::random::ErdosRenyi;
use webgraph::traits::SequentialLabeling;
use webgraph::transform;
use webgraph::{graphs::vec_graph::VecGraph, labels::Left};
use webgraph_algo::algo::exact_sum_sweep::*;
use webgraph_algo::algo::visits::Unbreakable;
use webgraph_algo::prelude::breadth_first::{EventPred, Seq};
use webgraph_algo::threads;
use webgraph_algo::traits::Sequential;

#[test]
fn test_path() -> Result<()> {
    let arcs = vec![(0, 1), (1, 2), (2, 1), (1, 0)];

    let mut vec_graph = VecGraph::new();
    for i in 0..3 {
        vec_graph.add_node(i);
    }
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);

    let sum_sweep = All::compute_undirected(&graph, &threads![], no_logging![]);

    assert_eq!(sum_sweep.eccentricities[0], 2);
    assert_eq!(sum_sweep.eccentricities[1], 1);
    assert_eq!(sum_sweep.eccentricities[2], 2);
    assert_eq!(sum_sweep.diameter, 2);
    assert_eq!(sum_sweep.radius, 1);
    assert_eq!(sum_sweep.radial_vertex, 1);
    assert!(sum_sweep.diameter == 2 || sum_sweep.diameter == 0);

    Ok(())
}

#[test]
fn test_star() -> Result<()> {
    let arcs = vec![
        (0, 1),
        (1, 0),
        (1, 2),
        (2, 1),
        (0, 3),
        (3, 0),
        (3, 4),
        (4, 3),
        (0, 5),
        (5, 0),
        (5, 6),
        (6, 5),
        (0, 7),
        (7, 0),
        (7, 8),
        (8, 7),
    ];

    let mut vec_graph = VecGraph::new();
    for i in 0..9 {
        vec_graph.add_node(i);
    }
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);

    let sum_sweep = All::compute_undirected(&graph, &threads![], no_logging![]);

    assert_eq!(sum_sweep.eccentricities[0], 2);
    assert_eq!(sum_sweep.eccentricities[1], 3);
    assert_eq!(sum_sweep.eccentricities[2], 4);
    assert_eq!(sum_sweep.eccentricities[3], 3);
    assert_eq!(sum_sweep.eccentricities[4], 4);
    assert_eq!(sum_sweep.eccentricities[5], 3);
    assert_eq!(sum_sweep.eccentricities[6], 4);
    assert_eq!(sum_sweep.eccentricities[7], 3);
    assert_eq!(sum_sweep.eccentricities[8], 4);

    assert_eq!(sum_sweep.diameter, 4);
    assert_eq!(sum_sweep.radius, 2);
    assert_eq!(sum_sweep.radial_vertex, 0);

    Ok(())
}

#[test]
fn test_lozenge() -> Result<()> {
    let arcs = vec![
        (0, 1),
        (1, 0),
        (0, 2),
        (2, 0),
        (1, 3),
        (3, 1),
        (2, 3),
        (3, 2),
    ];

    let mut vec_graph = VecGraph::new();
    for i in 0..4 {
        vec_graph.add_node(i);
    }
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);

    let sum_sweep = Radius::compute_undirected(&graph, &threads![], no_logging![]);

    assert_eq!(sum_sweep.radius, 2);

    Ok(())
}

#[test]
fn test_cycle() -> Result<()> {
    for size in [3, 5, 7] {
        let mut vec_graph = VecGraph::new();
        for i in 0..size {
            vec_graph.add_node(i);
        }
        for i in 0..size {
            if i == size - 1 {
                vec_graph.add_arc(i, 0);
                vec_graph.add_arc(0, i);
            } else {
                vec_graph.add_arc(i, i + 1);
                vec_graph.add_arc(i + 1, i);
            }
        }

        let graph = Left(vec_graph);

        let sum_sweep = RadiusDiameter::compute_undirected(&graph, &threads![], no_logging![]);

        assert_eq!(sum_sweep.diameter, size / 2);
        assert_eq!(sum_sweep.radius, size / 2);
    }
    Ok(())
}

#[test]
fn test_clique() -> Result<()> {
    for size in [10, 50, 100] {
        let mut vec_graph = VecGraph::new();
        for i in 0..size {
            vec_graph.add_node(i);
        }
        for i in 0..size {
            for j in 0..size {
                if i != j {
                    vec_graph.add_arc(i, j);
                }
            }
        }

        let graph = Left(vec_graph);

        let sum_sweep = All::compute_undirected(&graph, &threads![], no_logging![]);

        for i in 0..size {
            assert_eq!(sum_sweep.eccentricities[i], 1);
        }
        assert_eq!(sum_sweep.diameter, 1);
        assert_eq!(sum_sweep.radius, 1);
    }
    Ok(())
}

#[test]
fn test_no_edges() -> Result<()> {
    let mut vec_graph: VecGraph<()> = VecGraph::new();
    for i in 0..100 {
        vec_graph.add_node(i);
    }

    let graph = Left(vec_graph);

    let sum_sweep = All::compute_undirected(&graph, &threads![], no_logging![]);

    assert_eq!(sum_sweep.radius, 0);
    assert_eq!(sum_sweep.diameter, 0);

    Ok(())
}

#[allow(clippy::needless_range_loop)]
#[test]
fn test_sparse() -> Result<()> {
    let arcs = vec![(10, 32), (32, 10), (10, 65), (65, 10), (21, 44), (44, 21)];

    let mut vec_graph = VecGraph::new();
    for i in 0..100 {
        vec_graph.add_node(i);
    }
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);

    let sum_sweep = Radius::compute_undirected(&graph, &threads![], no_logging![]);

    assert_eq!(sum_sweep.radius, 1);

    Ok(())
}

#[test]
#[should_panic(expected = "Trying to build Radius without the radius computed")]
fn test_empty() {
    let vec_graph: VecGraph<()> = VecGraph::new();

    let graph = Left(vec_graph);

    Radius::compute_undirected(&graph, &threads![], no_logging![]);
}

#[allow(clippy::needless_range_loop)]
#[test]
fn test_er() -> Result<()> {
    for d in 2..=4 {
        let er = ErdosRenyi::new(100, (d as f64) / 100.0, 0);
        let graph = Left(VecGraph::from_lender(
            transform::simplify_sorted(er, 10000)?.iter(),
        ));

        let threads = threads![];

        let ess = All::compute_undirected(&graph, &threads, no_logging![]);

        let mut pll = Seq::new(&graph);
        let mut ecc = [0; 100];
        for node in 0..100 {
            pll.visit(
                node,
                |event| {
                    if let EventPred::Unknown { root, distance, .. } = event {
                        ecc[root] = ecc[root].max(distance);
                    }
                    Continue(())
                },
                no_logging![],
            )
            .unbreakable();
            pll.reset();
        }

        for node in 0..100 {
            assert_eq!(
                ess.eccentricities[node], ecc[node],
                "node = {}, actual = {}, expected = {}",
                node, ess.eccentricities[node], ecc[node]
            );
        }
    }

    Ok(())
}
