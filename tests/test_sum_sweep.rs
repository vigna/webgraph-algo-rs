use anyhow::Result;
use dsi_progress_logger::ProgressLogger;
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

    let mut sum_sweep =
        SumSweepDirectedDiameterRadius::new(&graph, &transposed, SumSweepOutputLevel::All, None)?;
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
    )?;
    sum_sweep.compute(Option::<ProgressLogger>::None)?;

    assert_eq!(sum_sweep.radius(), Some(2));
    assert_eq!(sum_sweep.radial_vertex(), Some(1));

    Ok(())
}
