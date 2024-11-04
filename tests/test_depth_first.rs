use dsi_progress_logger::ProgressLogger;
use webgraph::labels::proj::Left;
use webgraph::prelude::VecGraph;
use webgraph_algo::algo::{acyclicity, top_sort};

#[test]
fn test_top_sort() {
    assert_eq!(
        vec![0, 1, 2].into_boxed_slice(),
        top_sort::run(
            Left(VecGraph::from_arc_list([(1, 2), (0, 1)])),
            &mut Option::<ProgressLogger>::None
        )
    );

    assert_eq!(
        vec![0, 1, 2].into_boxed_slice(),
        top_sort::run(
            Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0)])),
            &mut Option::<ProgressLogger>::None
        )
    );

    assert_eq!(
        vec![0, 2, 1, 3].into_boxed_slice(),
        top_sort::run(
            Left(VecGraph::from_arc_list([(0, 1), (0, 2), (2, 3), (1, 3)])),
            &mut Option::<ProgressLogger>::None
        )
    );
}

#[test]
fn test_acyclicity() {
    assert!(
        acyclicity::run(
            Left(VecGraph::from_arc_list([(1, 2), (0, 1)])),
            &mut Option::<ProgressLogger>::None
        )
    );

    assert!(
        !acyclicity::run(
            Left(VecGraph::from_arc_list([(0, 1), (1, 2), (2, 0)])),
            &mut Option::<ProgressLogger>::None
        )
    );

    assert!(
        acyclicity::run(
            Left(VecGraph::from_arc_list([(0, 1), (0, 2), (2, 3), (1, 3)])),
            &mut Option::<ProgressLogger>::None
        )
    );
}
