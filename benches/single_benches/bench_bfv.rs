use super::params::*;
use criterion::{BenchmarkId, Criterion, Throughput};
use dsi_progress_logger::ProgressLogger;
use webgraph::graphs::BVGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::*;
use webgraph_algo::prelude::*;

struct Node {
    index: usize,
}

struct Factory {}

impl NodeVisit for Node {
    type VisitResult = usize;
    type AccumulatedResult = Vec<usize>;

    fn visit(self) -> Self::VisitResult {
        self.index
    }

    fn init_result() -> Self::AccumulatedResult {
        Vec::new()
    }

    fn accumulate_result(
        partial_result: &mut Self::AccumulatedResult,
        visit_result: Self::VisitResult,
    ) {
        partial_result.push(visit_result)
    }
}

impl NodeFactory for Factory {
    type Node = Node;

    fn node_from_index(&self, node_index: usize) -> Self::Node {
        Node { index: node_index }
    }
}

pub fn bench_bfv(c: &mut Criterion) {
    let mut group = c.benchmark_group("Breadth first visit");
    group.sampling_mode(criterion::SamplingMode::Flat);
    group.sample_size(NUM_SAMPLES);
    for graph in BENCH_GRAPHS {
        let graph = BVGraph::with_basename(graph).load().unwrap();
        let factory = Factory {};
        let input = (&graph, &factory);
        let parameter = format!("{} nodes", graph.num_nodes());
        group.throughput(Throughput::Elements(graph.num_nodes().try_into().unwrap()));

        group.bench_with_input(
            BenchmarkId::new("Sequential", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    SingleThreadedBreadthFirstVisit::with_start(i.0, i.1, 10000)
                        .visit(Option::<ProgressLogger>::None)
                        .unwrap()
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel exclusive", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    ParallelExclusiveBreadthFirstVisit::with_start(i.0, i.1, 10000)
                        .visit(Option::<ProgressLogger>::None)
                        .unwrap()
                });
            },
        );
    }
    group.finish();
}
