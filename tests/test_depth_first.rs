/*
 * SPDX-FileCopyrightText: 2024 Matteo Dell'Acqua
 * SPDX-FileCopyrightText: 2025 Sebastiano Vigna
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

use dsi_progress_logger::prelude::*;
use no_break::NoBreak;
use webgraph::prelude::VecGraph;
use webgraph_algo::{
    algo::{acyclicity, top_sort, traits::Acyclicity},
    prelude::depth_first,
    traits::Sequential,
};

#[test]
fn test_top_sort() {
    assert_eq!(
        vec![0, 1, 2].into_boxed_slice(),
        top_sort(VecGraph::from_arcs([(1, 2), (0, 1)]), no_logging![])
    );

    assert_eq!(
        vec![0, 1, 2].into_boxed_slice(),
        top_sort(VecGraph::from_arcs([(0, 1), (1, 2), (2, 0)]), no_logging![])
    );

    assert_eq!(
        vec![0, 2, 1, 3].into_boxed_slice(),
        top_sort(
            VecGraph::from_arcs([(0, 1), (0, 2), (2, 3), (1, 3)]),
            no_logging![]
        )
    );
}

#[test]
fn test_acyclicity() {
    let graph = VecGraph::from_arcs([(1, 2), (0, 1)]);

    assert!(acyclicity(&graph, no_logging![]));
    assert!(graph.is_acyclic());

    let graph = VecGraph::from_arcs([(0, 1), (1, 2), (2, 0)]);

    assert!(!acyclicity(&graph, no_logging![]));
    assert!(!graph.is_acyclic());

    let graph = VecGraph::from_arcs([(0, 1), (0, 2), (2, 3), (1, 3)]);

    assert!(acyclicity(&graph, no_logging![]));
    assert!(graph.is_acyclic());
}

#[test]
fn test_depth() {
    let graph = VecGraph::from_arcs([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]);
    depth_first::SeqNoPred::new(&graph)
        .visit([0], |event| {
            match event {
                depth_first::EventNoPred::Previsit { node, depth, .. } => {
                    assert_eq!(node, depth);
                }
                _ => (),
            }
            std::ops::ControlFlow::Continue(())
        })
        .continue_value_no_break();
}
