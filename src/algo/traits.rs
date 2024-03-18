pub trait NodeVisit {
    type VisitReturn;
    fn visit(self) -> Self::VisitReturn;
}

pub trait NodeFactory {
    type Node;
    fn node_from_index(&self, node_index: usize) -> Self::Node;
}
