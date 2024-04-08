use super::types::BreadthFirstVisitTree;
use anyhow::Result;
use dsi_progress_logger::ProgressLog;

/// A visitable graph that allows to compute Breadth First Visit trees.
pub trait GraphVisit {
    /// Computes and returns a Breadth First Visit tree.
    ///
    /// A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit.
    /// If `Option::<dsi_progress_logger::ProgressLogger>::None` is passed, logging code should
    /// be optimized away by the compiler.
    fn visit(self, pl: impl ProgressLog) -> Result<BreadthFirstVisitTree>;
}
