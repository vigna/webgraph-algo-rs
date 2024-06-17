use anyhow::Result;
use dsi_progress_logger::ProgressLog;

/// Flag used for [`DepthFirstGraphVisit`].
///
/// Specifies what event triggered the callback during the visit.
pub enum DepthFirstVisitEvent {
    /// Flag used for the first time a node is visited.
    Discover,
    /// Flag used for every time a node is encountered after the first.
    AlreadyVisited,
    /// Flag used when a node is completely visited and emitted as completed.
    Emit,
}

/// A visitable graph that allows to compute Depth First Visit trees.
pub trait DepthFirstGraphVisit {
    /// Starts a Depth first visit from every node and applies `callback` to every visited node with the
    /// appropriate flag. After this function returns, the visit is invalid.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit, its distance from it and the event flag.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit<C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync>(
        self,
        callback: C,
        pl: impl ProgressLog,
    ) -> Result<()>
    where
        Self: Sized,
    {
        self.visit_filtered(callback, |_, _, _, _| true, pl)
    }

    /// Visits depth-first the graph from the specified node and applies `callback` to every visited node
    /// with the appropriate flag.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit, its distance from it and the event flag.
    /// - `node_index`: The node to start the visit in.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_from_node<C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync>(
        &mut self,
        callback: C,
        node_index: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.visit_from_node_filtered(callback, |_, _, _, _| true, node_index, pl)
    }

    /// Starts a Depth first visit from every node and applies `callback` to every visited node with the
    /// apppropriate flag.
    /// Nodes are filtered with `filter` callable.
    /// After this function returns, the visit is invalid.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit, its distance from it and the event flag.
    /// - `filter`: A function or closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_filtered<
        C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync,
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

    /// Visits depth-first the graph from the specified node and applies `callback` to every visited node
    /// with the appropriate flag.
    /// Nodes are filtered with `filter` callable.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit, its distance from it and the event flag.
    /// - `filter`: A function or closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `node_index`: The node to start the visit in.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_from_node_filtered<
        C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        node_index: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()>;

    /// **Internal method. You should not need to call this directly.**
    ///
    /// Starts a Depth first visit from every node and applies `callback` to every visited node with
    /// the appropriate flag.
    /// Nodes are filtered with `filter` callable.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit, its distance from it and the event flag.
    /// - `filter`: A function or closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_graph_filtered<
        C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync,
        F: Fn(usize, usize, usize, usize) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        pl: &mut impl ProgressLog,
    ) -> Result<()>;
}

/// A reusable depth-first visitable graph to avoid reallocating the visit
pub trait ReusableDepthFirstGraphVisit: DepthFirstGraphVisit {
    /// Resets the visit status.
    fn reset(&mut self) -> Result<()>;

    /// Starts a Depth first visit from every node and applies `callback` to every visited node with
    /// the appropriate flag.
    /// Nodes are filtered with `filter` callable.
    /// After this function returns, the visit is still valid and may be used again.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit, its distance from it and the event flag.
    /// - `filter`: A function or closure that takes as arguments the node index, its parent, the root
    /// of the visit and its distance from it and returns `true` if the node should be visited,
    /// `false` otherwise.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_filtered_and_reuse<
        C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync,
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

    /// Starts a Depth first visit from every node and applies `callback` to every visited node with the
    /// appropriate flag.
    /// After this function returns, the visit is still valid and may be used again.
    ///
    /// # Arguments:
    /// - `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    /// of the visit, its distance from it and the event flag.
    /// - `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    /// method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    /// passed, logging code should be optimized away by the compiler.
    fn visit_and_reuse<C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync>(
        &mut self,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.visit_filtered_and_reuse(callback, |_, _, _, _| true, pl)
    }
}
