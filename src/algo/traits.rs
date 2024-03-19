use dsi_progress_logger::ProgressLog;

pub trait NodeVisit {
    type PartialResult;
    fn visit(self, partial_result: Self::PartialResult) -> Self::PartialResult;
    fn init_result() -> Self::PartialResult;
}

pub trait NodeFactory {
    type Node;
    fn node_from_index(&self, node_index: usize) -> Self::Node;
}

pub trait GraphVisit<N: NodeVisit> {
    fn visit(self, pl: &mut impl ProgressLog) -> N::PartialResult;
}
