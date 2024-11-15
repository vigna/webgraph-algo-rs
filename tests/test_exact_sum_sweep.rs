use anyhow::Result;
use dsi_progress_logger::no_logging;
use sux::bits::AtomicBitVec;
use unwrap_infallible::UnwrapInfallible;
use webgraph::graphs::random::ErdosRenyi;
use webgraph::traits::SequentialLabeling;
use webgraph::transform::transpose;
use webgraph::{graphs::vec_graph::VecGraph, labels::Left};
use webgraph_algo::algo::exact_sum_sweep::*;
use webgraph_algo::prelude::breadth_first::{EventPred, Seq};
use webgraph_algo::threads;
use webgraph_algo::traits::Sequential;

#[test]
fn test_ob() {
    let mut a = [1, 2, 3];
    let u = SyncUnsafeSlice::new(&mut a);
    let p = unsafe { u.get_mut(0) };
    let q = unsafe { u.get_mut(0) };
    *p = 0;
    *q = 1;
}

#[test]
fn test_path() -> Result<()> {
    let arcs = vec![(0, 1), (1, 2), (2, 1), (1, 0)];

    let mut vec_graph = VecGraph::new();
    for i in 0..3 {
        vec_graph.add_node(i);
    }
    let mut transposed_vec_graph = vec_graph.clone();
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
        transposed_vec_graph.add_arc(arc.1, arc.0);
    }

    let graph = Left(vec_graph);
    let transposed = Left(transposed_vec_graph);

    let sum_sweep = All::compute_directed(&graph, &transposed, None, &threads![], no_logging![]);

    assert_eq!(sum_sweep.forward_eccentricities[0], 2);
    assert_eq!(sum_sweep.forward_eccentricities[1], 1);
    assert_eq!(sum_sweep.forward_eccentricities[2], 2);
    assert_eq!(sum_sweep.backward_eccentricities[0], 2);
    assert_eq!(sum_sweep.diameter, 2);
    assert_eq!(sum_sweep.radius, 1);
    assert_eq!(sum_sweep.radial_vertex, 1);
    assert!(sum_sweep.diametral_vertex == 2 || sum_sweep.diametral_vertex == 0);

    Ok(())
}

#[test]
fn test_many_scc() -> Result<()> {
    let arcs = vec![
        (0, 1),
        (1, 0),
        (1, 2),
        (2, 1),
        (6, 2),
        (2, 6),
        (3, 4),
        (4, 3),
        (4, 5),
        (5, 4),
        (0, 3),
        (0, 4),
        (1, 5),
        (1, 4),
        (2, 5),
    ];
    let transposed_arcs = arcs.iter().map(|(a, b)| (*b, *a)).collect::<Vec<_>>();

    let graph = Left(VecGraph::from_arc_list(arcs));
    let transposed = Left(VecGraph::from_arc_list(transposed_arcs));

    let sum_sweep = All::compute_directed(&graph, &transposed, None, &threads![], no_logging![]);

    assert_eq!(sum_sweep.radius, 2);
    assert_eq!(sum_sweep.radial_vertex, 1);

    Ok(())
}

#[test]
fn test_lozenge() -> Result<()> {
    let arcs = vec![(0, 1), (1, 0), (0, 2), (1, 3), (2, 3)];

    let mut vec_graph = VecGraph::new();
    for i in 0..4 {
        vec_graph.add_node(i);
    }
    let mut transposed_vec_graph = vec_graph.clone();
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
        transposed_vec_graph.add_arc(arc.1, arc.0);
    }

    let graph = Left(vec_graph);
    let transposed = Left(transposed_vec_graph);

    let sum_sweep = Radius::compute_directed(&graph, &transposed, None, &threads![], no_logging![]);

    assert_eq!(sum_sweep.radius, 2);
    assert!(sum_sweep.radial_vertex == 0 || sum_sweep.radial_vertex == 1);

    Ok(())
}

#[test]
fn test_many_dir_path() -> Result<()> {
    let arcs = vec![
        (0, 1),
        (1, 2),
        (2, 3),
        (3, 4),
        (5, 6),
        (6, 7),
        (7, 8),
        (8, 9),
        (9, 10),
        (10, 18),
        (11, 12),
        (13, 14),
        (14, 15),
        (15, 16),
        (16, 17),
    ];

    let mut vec_graph = VecGraph::new();
    for i in 0..19 {
        vec_graph.add_node(i);
    }
    let mut transposed_vec_graph = vec_graph.clone();
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
        transposed_vec_graph.add_arc(arc.1, arc.0);
    }

    let graph = Left(vec_graph);
    let transposed = Left(transposed_vec_graph);
    let radial_vertices = AtomicBitVec::new(19);
    radial_vertices.set(16, true, std::sync::atomic::Ordering::Relaxed);
    radial_vertices.set(8, true, std::sync::atomic::Ordering::Relaxed);

    let sum_sweep = All::compute_directed(
        &graph,
        &transposed,
        Some(radial_vertices),
        &threads![],
        no_logging![],
    );

    assert_eq!(sum_sweep.diameter, 6);
    assert_eq!(sum_sweep.radius, 1);
    assert_eq!(sum_sweep.radial_vertex, 16);
    assert!(sum_sweep.diametral_vertex == 5 || sum_sweep.diametral_vertex == 18);

    Ok(())
}

#[test]
fn test_cycle() -> Result<()> {
    for size in [3, 5, 7] {
        let mut vec_graph = VecGraph::new();
        for i in 0..size {
            vec_graph.add_node(i);
        }
        let mut transposed_vec_graph = vec_graph.clone();
        for i in 0..size {
            if i == size - 1 {
                vec_graph.add_arc(i, 0);
                transposed_vec_graph.add_arc(0, i);
            } else {
                vec_graph.add_arc(i, i + 1);
                transposed_vec_graph.add_arc(i + 1, i);
            }
        }

        let graph = Left(vec_graph);
        let transposed = Left(transposed_vec_graph);

        let sum_sweep =
            RadiusDiameter::compute_directed(&graph, &transposed, None, &threads![], no_logging![]);

        assert_eq!(sum_sweep.diameter, size - 1);
        assert_eq!(sum_sweep.radius, size - 1);
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

        let graph = Left(vec_graph.clone());
        let transposed = Left(vec_graph);
        let radial_vertices = AtomicBitVec::new(size);
        let rngs = [
            rand::random::<usize>() % size,
            rand::random::<usize>() % size,
            rand::random::<usize>() % size,
        ];
        radial_vertices.set(rngs[0], true, std::sync::atomic::Ordering::Relaxed);
        radial_vertices.set(rngs[1], true, std::sync::atomic::Ordering::Relaxed);
        radial_vertices.set(rngs[2], true, std::sync::atomic::Ordering::Relaxed);

        let sum_sweep = All::compute_directed(
            &graph,
            &transposed,
            Some(radial_vertices),
            &threads![],
            no_logging![],
        );

        for i in 0..size {
            assert_eq!(sum_sweep.forward_eccentricities[i], 1);
        }
        assert!(rngs.contains(&sum_sweep.radial_vertex));
    }
    Ok(())
}

#[test]
fn test_empty() -> Result<()> {
    let mut vec_graph: VecGraph<()> = VecGraph::new();
    for i in 0..100 {
        vec_graph.add_node(i);
    }

    let graph = Left(vec_graph.clone());
    let transposed = Left(vec_graph);

    let sum_sweep = All::compute_directed(&graph, &transposed, None, &threads![], no_logging![]);

    assert_eq!(sum_sweep.radius, 0);
    assert_eq!(sum_sweep.diameter, 0);

    Ok(())
}

#[test]
fn test_sparse() -> Result<()> {
    let arcs = vec![(10, 32), (10, 65), (65, 10), (21, 44)];

    let mut vec_graph = VecGraph::new();
    for i in 0..100 {
        vec_graph.add_node(i);
    }
    let mut transposed_vec_graph = vec_graph.clone();
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
        transposed_vec_graph.add_arc(arc.1, arc.0);
    }

    let graph = Left(vec_graph);
    let transposed = Left(transposed_vec_graph);

    let sum_sweep = All::compute_directed(&graph, &transposed, None, &threads![], no_logging![]);

    assert_eq!(sum_sweep.radius, 1);
    assert_eq!(sum_sweep.radial_vertex, 10);

    Ok(())
}

#[test]
fn test_no_radial_vertices() -> Result<()> {
    let arcs = vec![(0, 1)];

    let mut vec_graph = VecGraph::new();
    for i in 0..2 {
        vec_graph.add_node(i);
    }
    let mut transposed_vec_graph = vec_graph.clone();
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
        transposed_vec_graph.add_arc(arc.1, arc.0);
    }

    let graph = Left(vec_graph);
    let transposed = Left(transposed_vec_graph);
    let radial_vertices = AtomicBitVec::new(2);

    let sum_sweep = All::compute_directed(
        &graph,
        &transposed,
        Some(radial_vertices),
        &threads![],
        no_logging![],
    );

    assert_eq!(sum_sweep.radius, usize::MAX);

    Ok(())
}

#[test]
#[should_panic(expected = "Trying to build All without all eccentricities computed")]
fn test_empty_graph() {
    let vec_graph: VecGraph<()> = VecGraph::new();

    let graph = Left(vec_graph.clone());
    let transposed = Left(vec_graph);

    All::compute_directed(&graph, &transposed, None, &threads![], no_logging![]);
}

#[test]
fn test_graph_no_edges() -> Result<()> {
    let mut vec_graph: VecGraph<()> = VecGraph::new();
    for i in 0..2 {
        vec_graph.add_node(i);
    }

    let graph = Left(vec_graph.clone());
    let transposed = Left(vec_graph);

    let sum_sweep = All::compute_directed(&graph, &transposed, None, &threads![], no_logging![]);

    assert_eq!(sum_sweep.radius, 0);
    assert_eq!(sum_sweep.diameter, 0);

    Ok(())
}

#[test]
fn test_er() -> Result<()> {
    for d in 2..=4 {
        let graph = Left(VecGraph::from_lender(
            ErdosRenyi::new(100, (d as f64) / 100.0, 0).iter(),
        ));

        let transpose = Left(VecGraph::from_lender(transpose(&graph, 10000)?.iter()));

        let threads = threads![];

        let ess = All::compute_directed(&graph, transpose, None, &threads, no_logging![]);

        let mut pll = Seq::new(&graph);
        let mut ecc = [0; 100];
        for node in 0..100 {
            pll.visit(
                node,
                |event| {
                    if let EventPred::Unknown { root, distance, .. } = event {
                        ecc[root] = ecc[root].max(distance);
                    }
                    Ok(())
                },
                no_logging![],
            )
            .unwrap_infallible();
            pll.reset();
        }

        for node in 0..100 {
            assert_eq!(
                ess.forward_eccentricities[node], ecc[node],
                "node = {}, actual = {}, expected = {}",
                node, ess.backward_eccentricities[node], ecc[node]
            );
        }
    }

    Ok(())
}
