use anyhow::Result;
use dsi_progress_logger::ProgressLog;

pub trait NodeVisit {
    type AccumulatedResult;
    type VisitResult;
    fn visit(self) -> Self::VisitResult;
    fn accumulate_result(
        partial_result: Self::AccumulatedResult,
        visit_result: Self::VisitResult,
    ) -> Self::AccumulatedResult;
    fn init_result() -> Self::AccumulatedResult;
}

pub trait NodeFactory {
    type Node;
    fn node_from_index(&self, node_index: usize) -> Self::Node;
}

pub trait GraphVisit<N: NodeVisit> {
    fn visit(self, pl: impl ProgressLog) -> Result<N::AccumulatedResult>;
}
