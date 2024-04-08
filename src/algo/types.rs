pub struct BreadthFirstVisitTree {
    pub order: Vec<usize>,
    cuts: Vec<usize>,
}

pub struct BreadthFirstVisitTreeBuilder {
    order: Vec<usize>,
    cuts: Vec<usize>,
}

impl BreadthFirstVisitTreeBuilder {
    pub fn new() -> BreadthFirstVisitTreeBuilder {
        BreadthFirstVisitTreeBuilder {
            order: Vec::new(),
            cuts: Vec::new(),
        }
    }

    pub fn push_node(&mut self, node_index: usize) {
        self.order.push(node_index)
    }

    pub fn push_nodes(&mut self, mut nodes: Vec<usize>) {
        self.order.append(&mut nodes)
    }

    pub fn cut(&mut self) {
        self.cuts.push(self.order.len() - 1)
    }

    pub fn build(self) -> BreadthFirstVisitTree {
        BreadthFirstVisitTree {
            order: self.order,
            cuts: self.cuts,
        }
    }
}

impl BreadthFirstVisitTree {
    pub fn get_by_order(&self, index: usize) -> usize {
        self.order[index]
    }

    pub fn get_by_distance(&self, distance: usize) -> Vec<usize> {
        let first_index = self.cuts[distance];
        let last_index = if distance >= self.cuts.len() + 1 {
            self.order.len() - 1
        } else {
            self.cuts[distance + 1]
        };
        self.order[first_index..last_index].to_owned()
    }
}
