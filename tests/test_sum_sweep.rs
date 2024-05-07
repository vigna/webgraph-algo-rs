use anyhow::Result;
use dsi_progress_logger::ProgressLogger;
use sux::bits::AtomicBitVec;
use webgraph::traits::SequentialLabeling;
use webgraph::transform::transpose;
use webgraph::{graphs::vec_graph::VecGraph, labels::Left};
use webgraph_algo::algo::diameter::{SumSweepDirectedDiameterRadius, SumSweepOutputLevel};

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
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::All,
        None,
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.eccentricity(0, true), Some(2));
    assert_eq!(sum_sweep.eccentricity(1, true), Some(1));
    assert_eq!(sum_sweep.eccentricity(2, true), Some(2));
    assert_eq!(sum_sweep.eccentricity(0, false), Some(2));
    assert_eq!(sum_sweep.diameter(), Some(2));
    assert_eq!(sum_sweep.radius(), Some(1));
    assert_eq!(sum_sweep.radial_vertex(), Some(1));
    assert!(sum_sweep.diametral_vertex() == Some(2) || sum_sweep.diametral_vertex() == Some(0));

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

    let mut vec_graph = VecGraph::new();
    for i in 0..7 {
        vec_graph.add_node(i);
    }
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::Radius,
        None,
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(2));
    assert_eq!(sum_sweep.radial_vertex(), Some(1));

    Ok(())
}

#[test]
fn test_lozenge() -> Result<()> {
    let arcs = vec![(0, 1), (1, 0), (0, 2), (1, 3), (2, 3)];

    let mut vec_graph = VecGraph::new();
    for i in 0..4 {
        vec_graph.add_node(i);
    }
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::Radius,
        None,
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(2));
    assert!(sum_sweep.radial_vertex() == Some(0) || sum_sweep.radial_vertex() == Some(1));
    assert!(sum_sweep.eccentricity(sum_sweep.radial_vertex().unwrap(), true) == sum_sweep.radius());

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
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));
    let radial_vertices = AtomicBitVec::new(19);
    radial_vertices.set(16, true, std::sync::atomic::Ordering::Relaxed);
    radial_vertices.set(8, true, std::sync::atomic::Ordering::Relaxed);

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::All,
        Some(radial_vertices),
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.diameter(), Some(6));
    assert_eq!(sum_sweep.radius(), Some(1));
    assert_eq!(sum_sweep.radial_vertex(), Some(16));
    assert!(sum_sweep.diametral_vertex() == Some(5) || sum_sweep.diametral_vertex() == Some(18));

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
            } else {
                vec_graph.add_arc(i, i + 1);
            }
        }

        let graph = Left(vec_graph);
        let transposed = Left(VecGraph::from_labeled_lender(
            transpose(&graph, 32)?.0.iter(),
        ));

        let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
            &graph,
            &transposed,
            SumSweepOutputLevel::RadiusDiameter,
            None,
            Option::<std::path::PathBuf>::None,
            Option::<ProgressLogger>::None,
        )?;
        sum_sweep.compute(Option::<ProgressLogger>::None)?;

        assert_eq!(sum_sweep.diameter(), Some(size - 1));
        assert_eq!(sum_sweep.radius(), Some(size - 1));
        assert_eq!(
            sum_sweep.eccentricity(sum_sweep.radial_vertex().unwrap(), true),
            sum_sweep.radius()
        );
        assert_eq!(
            sum_sweep.eccentricity(sum_sweep.diametral_vertex().unwrap(), true),
            sum_sweep.diameter()
        );
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
        let transposed = Left(VecGraph::from_labeled_lender(
            transpose(&graph, 32)?.0.iter(),
        ));
        let radial_vertices = AtomicBitVec::new(size);
        let rngs = [
            rand::random::<usize>() % size,
            rand::random::<usize>() % size,
            rand::random::<usize>() % size,
        ];
        radial_vertices.set(rngs[0], true, std::sync::atomic::Ordering::Relaxed);
        radial_vertices.set(rngs[1], true, std::sync::atomic::Ordering::Relaxed);
        radial_vertices.set(rngs[2], true, std::sync::atomic::Ordering::Relaxed);

        let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
            &graph,
            &transposed,
            SumSweepOutputLevel::All,
            Some(radial_vertices),
            Option::<std::path::PathBuf>::None,
            Option::<ProgressLogger>::None,
        )?;
        sum_sweep.compute(Option::<ProgressLogger>::None)?;

        for i in 0..size {
            assert_eq!(sum_sweep.eccentricity(i, true), Some(1));
        }
        assert!(rngs.contains(&sum_sweep.radial_vertex().unwrap()));
    }
    Ok(())
}

#[test]
fn test_empty() -> Result<()> {
    let mut vec_graph = VecGraph::new();
    for i in 0..100 {
        vec_graph.add_node(i);
    }

    let graph = Left(vec_graph);
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::All,
        None,
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(0));
    assert_eq!(sum_sweep.diameter(), Some(0));

    Ok(())
}

#[test]
fn test_sparse() -> Result<()> {
    let arcs = vec![(10, 32), (10, 65), (65, 10), (21, 44)];

    let mut vec_graph = VecGraph::new();
    for i in 0..100 {
        vec_graph.add_node(i);
    }
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::Radius,
        None,
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(1));
    assert_eq!(sum_sweep.radial_vertex(), Some(10));

    Ok(())
}

#[test]
fn test_no_radial_vertices() -> Result<()> {
    let arcs = vec![(0, 1)];

    let mut vec_graph = VecGraph::new();
    for i in 0..2 {
        vec_graph.add_node(i);
    }
    for arc in arcs {
        vec_graph.add_arc(arc.0, arc.1);
    }

    let graph = Left(vec_graph);
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));
    let radial_vertices = AtomicBitVec::new(2);

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::All,
        Some(radial_vertices),
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(isize::MAX as usize));

    Ok(())
}

#[test]
fn test_empty_graph() -> Result<()> {
    let vec_graph = VecGraph::new();

    let graph = Left(vec_graph);
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::All,
        None,
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), None);
    assert_eq!(sum_sweep.diameter(), None);

    Ok(())
}

#[test]
fn test_graph_no_edges() -> Result<()> {
    let mut vec_graph = VecGraph::new();
    for i in 0..2 {
        vec_graph.add_node(i);
    }

    let graph = Left(vec_graph);
    let transposed = Left(VecGraph::from_labeled_lender(
        transpose(&graph, 32)?.0.iter(),
    ));

    let mut sum_sweep = SumSweepDirectedDiameterRadius::new(
        &graph,
        &transposed,
        SumSweepOutputLevel::Radius,
        None,
        Option::<std::path::PathBuf>::None,
        Option::<ProgressLogger>::None,
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(0));
    assert_eq!(sum_sweep.diameter(), Some(0));

    Ok(())
}
