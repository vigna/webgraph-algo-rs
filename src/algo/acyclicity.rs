/*
 * SPDX-FileCopyrightText: 2024 Matteo Dell'Acqua
 * SPDX-FileCopyrightText: 2025 Sebastiano Vigna
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

use crate::{
    algo::visits::depth_first::*, algo::visits::Sequential, algo::visits::StoppedWhenDone,
};
use dsi_progress_logger::prelude::*;
use std::ops::ControlFlow::{Break, Continue};
use webgraph::traits::RandomAccessGraph;

/// Runs an acyclicity test.
pub fn acyclicity(graph: impl RandomAccessGraph, pl: &mut impl ProgressLog) -> bool {
    let num_nodes = graph.num_nodes();
    pl.item_name("node");
    pl.expected_updates(Some(num_nodes));
    pl.start("Checking acyclicity");

    let mut visit = SeqPath::new(&graph);

    let acyclic = visit.visit(0..num_nodes, |event| {
        // Stop the visit as soon as a back edge is found.
        match event {
            EventPred::Previsit { .. } => {
                pl.light_update();
                Continue(())
            }
            EventPred::Revisit { on_stack: true, .. } => Break(StoppedWhenDone {}),
            _ => Continue(()),
        }
    });

    pl.done();
    acyclic.is_continue()
}

/// Trait providing an easy way to test a [`RandomAccessGraph`] for
/// acyclicity.
///
/// # Examples
/// ```
/// use webgraph::prelude::VecGraph;
/// use webgraph_algo::traits::Acyclicity;
///
/// // This is an acyclic graph
/// let graph = VecGraph::from_arcs([(1, 2), (0, 1)]);
/// assert!(graph.is_acyclic());
///
/// // This graph contains a cycle
/// let graph = VecGraph::from_arcs([(0, 1), (1, 2), (2, 0)]);
/// assert!(!graph.is_acyclic());
/// ```
pub trait Acyclicity {
    /// Returns whether the graph is acyclic.
    fn is_acyclic(&self) -> bool;
}

impl<G: RandomAccessGraph> Acyclicity for G {
    #[inline(always)]
    fn is_acyclic(&self) -> bool {
        acyclicity(self, no_logging![])
    }
}
