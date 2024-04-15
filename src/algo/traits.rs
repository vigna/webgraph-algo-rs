use anyhow::Result;
use dsi_progress_logger::ProgressLog;

/// A visitable graph that allows to compute Breadth First Visit trees.
pub trait GraphVisit {
    /// Computes a Breadth First Visit tree and applies `callback` to every visited node.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index and its distance from the
    /// starting node.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit<F: Fn(usize, usize) + Sync>(self, callback: F, pl: impl ProgressLog) -> Result<()>;

    /// Visits the connected component from the specified node and applies `callback` to every visited node.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index and its distance from the
    /// starting node.
    /// - `node_index`: The node to start the visit in.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_component<F: Fn(usize, usize) + Sync>(
        &mut self,
        callback: F,
        node_index: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()>;
}
