use anyhow::Result;
use dsi_progress_logger::ProgressLog;

/// A visitable node.
///
/// It allows graph visits by providing implementations on how to visit
/// the node and specifying what to return.
pub trait NodeVisit {
    /// The type of data that is returned when the visit finishes.
    ///
    /// It is obtained by accumulating the results of the single nodes.
    type AccumulatedResult;
    /// The type of data that is returned when a node is visited.
    type VisitResult;
    /// Visits the node and returns the relevant data.
    fn visit(self) -> Self::VisitResult;
    /// Accumulates the partial result with the current visit.
    ///
    /// # Arguments:
    /// - `partial_result`: the mutable reference to the partial result.
    /// - `visit_result`: the visit result of the current node.
    fn accumulate_result(
        partial_result: &mut Self::AccumulatedResult,
        visit_result: Self::VisitResult,
    );
    /// Initializes the partial result.
    fn init_result() -> Self::AccumulatedResult;
}

/// A factory that creates nodes from their index.
pub trait NodeFactory {
    /// The type of nods that are returned by this factory.
    type Node;
    /// Returns the node corresponding to the given `node_index`.
    fn node_from_index(&self, node_index: usize) -> Self::Node;
}

/// A visitable graph that allows to run custom code during the visit in order to derive data.
pub trait GraphVisit<N: NodeVisit> {
    /// Visits the graph and returns the accumulated final result.
    ///
    /// A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit.
    /// If `Option::<dsi_progress_logger::ProgressLogger>::None` is passed, logging code should
    /// be optimized away by the compiler.
    fn visit(self, pl: impl ProgressLog) -> Result<N::AccumulatedResult>;
}
