use anyhow::Result;
use dsi_progress_logger::ProgressLog;

pub enum DepthFirstVisitEvent {
    Discover,
    AlreadyVisited,
    Emit,
}

pub trait DepthFirstGraphVisit {
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

    fn visit_from_node<C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync>(
        &mut self,
        callback: C,
        node_index: usize,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.visit_from_node_filtered(callback, |_, _, _, _| true, node_index, pl)
    }

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

    fn visit_and_reuse<C: Fn(usize, usize, usize, usize, DepthFirstVisitEvent) + Sync>(
        &mut self,
        callback: C,
        pl: &mut impl ProgressLog,
    ) -> Result<()> {
        self.visit_filtered_and_reuse(callback, |_, _, _, _| true, pl)
    }
}
