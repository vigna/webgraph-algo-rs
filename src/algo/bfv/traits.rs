use anyhow::Result;
use dsi_progress_logger::ProgressLog;

/// A visitable graph that allows to compute Breadth First Visit trees.
pub trait BreadthFirstGraphVisit {
    /// Starts a Breadth first visit from every node and applies `callback` to every visited node.
    /// After this function returns, the visit is invalid.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit<C: Fn(usize, usize, usize, usize) + Sync>(
        self,
        callback: C,
        pl: impl ProgressLog,
    ) -> Result<()>
    where
        Self: Sized,
    {
        self.visit_filtered(callback, |_, _, _, _| true, pl)
    }

    /// Visits breadth-first the graph from the specified node and applies `callback` to every visited node.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it.
    /// - `visit_root`: The node to start the visit in.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_from_node<C: Fn(usize, usize, usize, usize) + Sync>(
        &mut self,
        callback: C,
        visit_root: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.visit_from_node_filtered(callback, |_, _, _, _| true, visit_root, pl)
    }

    /// Starts a Breadth first visit from every node and applies `callback` to every visited node.
    /// Nodes are filtered with `filter` callable.
    /// After this function returns, the visit is invalid.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it.
    /// - `filter`: A function or closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_filtered<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        mut self,
        callback: C,
        filter: F,
        mut pl: impl ProgressLog,
    ) -> Result<()>
    where
        Self: Sized,
    {
        self.visit_graph_filtered(callback, filter, &mut pl)
    }

    /// Visits breadth-first the graph from the specified node and applies `callback` to every visited node.
    /// Nodes are filtered with `filter` callable.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it.
    /// - `filter`: A function or closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `visit_root`: The node to start the visit in.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_from_node_filtered<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        visit_root: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()>;

    /// **Internal method. You should not need to call this directly.**
    ///
    /// Starts a Breadth first visit from every node and applies `callback` to every visited node.
    /// Nodes are filtered with `filter` callable.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it.
    /// - `filter`: A function or closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_graph_filtered<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<()>;
}

/// A reusable breadth-first visitable graph to avoid reallocating the visit
pub trait ReusableBreadthFirstGraphVisit: BreadthFirstGraphVisit {
    /// Resets the visit status.
    fn reset(&mut self) -> Result<()>;

    /// Starts a Breadth first visit from every node and applies `callback` to every visited node.
    /// Nodes are filtered with `filter` callable.
    /// After this function returns, the visit is still valid and may be used again.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it.
    /// - `filter`: A function or closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_filtered_and_reuse<
        C: Fn(usize, usize, usize, usize) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.visit_graph_filtered(callback, filter, pl)?;
        self.reset()?;
        Ok(())
    }

    /// Starts a Breadth first visit from every node and applies `callback` to every visited node.
    /// After this function returns, the visit is still valid and may be used again.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_and_reuse<C: Fn(usize, usize, usize, usize) + Sync>(
        &mut self,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.visit_filtered_and_reuse(callback, |_, _, _, _| true, pl)
    }
}
