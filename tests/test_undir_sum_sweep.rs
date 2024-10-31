use anyhow::Result;
use dsi_progress_logger::ProgressLogger;
use webgraph::{graphs::vec_graph::VecGraph, labels::Left};
use webgraph_algo::algo::diameter::*;

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

    let mut sum_sweep =
        SumSweepUndirectedDiameterRadiusBuilder::new(&graph, SumSweepOutputLevel::All)
            .build(&mut Option::<ProgressLogger>::None);
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.eccentricity(0), Some(2));
    assert_eq!(sum_sweep.eccentricity(1), Some(1));
    assert_eq!(sum_sweep.eccentricity(2), Some(2));
    assert_eq!(sum_sweep.diameter(), Some(2));
    assert_eq!(sum_sweep.radius(), Some(1));
    assert_eq!(sum_sweep.radial_vertex(), Some(1));
    assert!(sum_sweep.diameter() == Some(2) || sum_sweep.diameter() == Some(0));

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

    let mut sum_sweep =
        SumSweepUndirectedDiameterRadiusBuilder::new(&graph, SumSweepOutputLevel::All)
            .build(&mut Option::<ProgressLogger>::None);
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.eccentricity(0), Some(2));
    assert_eq!(sum_sweep.eccentricity(1), Some(3));
    assert_eq!(sum_sweep.eccentricity(2), Some(4));
    assert_eq!(sum_sweep.eccentricity(3), Some(3));
    assert_eq!(sum_sweep.eccentricity(4), Some(4));
    assert_eq!(sum_sweep.eccentricity(5), Some(3));
    assert_eq!(sum_sweep.eccentricity(6), Some(4));
    assert_eq!(sum_sweep.eccentricity(7), Some(3));
    assert_eq!(sum_sweep.eccentricity(8), Some(4));

    assert_eq!(sum_sweep.diameter(), Some(4));
    assert_eq!(sum_sweep.radius(), Some(2));
    assert_eq!(sum_sweep.radial_vertex(), Some(0));

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

    let mut sum_sweep =
        SumSweepUndirectedDiameterRadiusBuilder::new(&graph, SumSweepOutputLevel::Radius)
            .build(&mut Option::<ProgressLogger>::None);
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(2));
    assert!(sum_sweep.eccentricity(sum_sweep.radial_vertex().unwrap()) == sum_sweep.radius());

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

        let mut sum_sweep = SumSweepUndirectedDiameterRadiusBuilder::new(
            &graph,
            SumSweepOutputLevel::RadiusDiameter,
        )
        .build(&mut Option::<ProgressLogger>::None);
        sum_sweep.compute(Option::<ProgressLogger>::None)?;

        assert_eq!(sum_sweep.diameter(), Some(size / 2));
        assert_eq!(sum_sweep.radius(), Some(size / 2));

        assert!(sum_sweep.eccentricity(sum_sweep.radial_vertex().unwrap()) == sum_sweep.radius());
        assert!(
            sum_sweep.eccentricity(sum_sweep.diametral_vertex().unwrap()) == sum_sweep.diameter()
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

        let mut sum_sweep =
            SumSweepUndirectedDiameterRadiusBuilder::new(&graph, SumSweepOutputLevel::All)
                .build(&mut Option::<ProgressLogger>::None);
        sum_sweep.compute(Option::<ProgressLogger>::None)?;

        for i in 0..size {
            assert_eq!(sum_sweep.eccentricity(i), Some(1));
        }
        assert_eq!(sum_sweep.diameter(), Some(1));
        assert_eq!(sum_sweep.radius(), Some(1));
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

    let mut sum_sweep =
        SumSweepUndirectedDiameterRadiusBuilder::new(&graph, SumSweepOutputLevel::All)
            .build(&mut Option::<ProgressLogger>::None);
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(0));
    assert_eq!(sum_sweep.diameter(), Some(0));

    Ok(())
}

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

    let mut sum_sweep =
        SumSweepUndirectedDiameterRadiusBuilder::new(&graph, SumSweepOutputLevel::Radius)
            .build(&mut Option::<ProgressLogger>::None);
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(1));

    Ok(())
}

#[test]
fn test_empty() -> Result<()> {
    let vec_graph: VecGraph<()> = VecGraph::new();

    let graph = Left(vec_graph);

    let mut sum_sweep =
        SumSweepUndirectedDiameterRadiusBuilder::new(&graph, SumSweepOutputLevel::Radius)
            .build(&mut Option::<ProgressLogger>::None);
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), None);
    assert_eq!(sum_sweep.diameter(), None);

    Ok(())
}
