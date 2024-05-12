use anyhow::Result;
use dsi_progress_logger::ProgressLog;

/// A visitable graph that allows to compute Breadth First Visit trees.
pub trait GraphVisit {
    /// Starts a Breadth first visit from every node and applies `callback` to every visited node.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index and its distance from the
    /// starting node.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit<C: Fn(usize, usize) + Sync>(self, callback: C, pl: impl ProgressLog) -> Result<()>
    where
        Self: Sized,
    {
        self.filtered_visit(callback, |_, _, _| true, pl)
    }

    /// Visits the connected component from the specified node and applies `callback` to every visited node.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index and its distance from the
    /// starting node.
    /// - `node_index`: The node to start the visit in.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_component<C: Fn(usize, usize) + Sync>(
        &mut self,
        callback: C,
        node_index: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.filtered_component_visit(callback, |_, _, _| true, node_index, pl)
    }

    /// Starts a Breadth first visit from every node and applies `callback` to every visited node.
    /// Nodes are filtered with `filter` callable.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index and its distance from the
    /// starting node.
    /// - `filter`: A function or closure that takes as arguments the node index, the index of the root of
    /// the visit and the distance from the root to the node and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn filtered_visit<C: Fn(usize, usize) + Sync, F: Fn(usize, usize, usize) -> bool + Sync>(
        self,
        callback: C,
        filter: F,
        pl: impl ProgressLog,
    ) -> Result<()>;

    /// Visits the connected component from the specified node and applies `callback` to every visited node.
    /// Nodes are filtered with `filter` callable.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index and its distance from the
    /// starting node.
    /// - `filter`: A function or closure that takes as arguments the node index, the index of the root of
    /// the visit and the distance from the root to the node and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `node_index`: The node to start the visit in.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn filtered_component_visit<
        C: Fn(usize, usize) + Sync,
        F: Fn(usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        node_index: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()>;
}
