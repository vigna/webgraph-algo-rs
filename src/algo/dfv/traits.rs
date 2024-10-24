use anyhow::Result;
use dsi_progress_logger::ProgressLog;

/// Flag used for [`DepthFirstGraphVisit`].
///
/// Specifies what event triggered the callback during the visit.
#[derive(Debug)]
pub enum DepthFirstVisitEvent {
    /// Flag used for the first time a node is visited.
    Discover,
    /// Flag used for every time a node is encountered after the first.
    AlreadyVisited,
    /// Flag used when a node is completely visited and emitted as completed.
    Emit,
}

#[derive(Debug, Clone, Copy)]
pub struct DFVArgs {
    /// The node index
    pub node_index: usize,
    /// The parent of [`Self::node_index`]
    pub parent: usize,
    /// The root of the current visit tree
    pub root: usize,
    /// The distance of [`Self::node_index`] from [`Self::root`]
    pub distance_from_root: usize,
}

/// A visitable graph that allows to compute Depth First Visit trees.
pub trait DepthFirstGraphVisit {
    /// Visits depth-first the graph from the specified node and applies `callback` to every visited node
    /// with the appropriate flag.
    ///
    /// # Arguments:
    /// * `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    ///   of the visit, its distance from it and the event flag.
    /// * `visit_root`: The node to start the visit in.
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    #[inline(always)]
    fn visit_from_node<C: Fn(DFVArgs, DepthFirstVisitEvent) + Sync>(
        &mut self,
        callback: C,
        visit_root: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.visit_from_node_filtered(callback, |_| true, visit_root, pl)
    }

    /// Visits depth-first the graph from the specified node and applies `callback` to every visited node
    /// with the appropriate flag.
    /// Nodes are filtered with `filter` callable.
    ///
    /// # Arguments:
    /// * `callback`: A function or a closure that takes as arguments the node index, its parent, the root
    ///   of the visit, its distance from it and the event flag.
    /// * `filter`: A function or closure that takes as arguments the node index, its parent, the root
    ///   of the visit and its distance from it and returns `true` if the node should be visited,
    ///   `false` otherwise.
    /// * `visit_root`: The node to start the visit in.
    /// * `pl`: A progress logger that implements [`dsi_progress_logger::ProgressLog`] may be passed to the
    ///   method to log the progress of the visit. If `Option::<dsi_progress_logger::ProgressLogger>::None` is
    ///   passed, logging code should be optimized away by the compiler.
    fn visit_from_node_filtered<
        C: Fn(DFVArgs, DepthFirstVisitEvent) + Sync,
        F: Fn(DFVArgs) -> bool + Sync,
    >(
        &mut self,
        callback: C,
        filter: F,
        visit_root: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()>;

    /// Resets the visit status.
    fn reset(&mut self) -> Result<()>;
}
