use super::params::*;
use criterion::{BenchmarkId, Criterion, Throughput};
use dsi_progress_logger::ProgressLogger;
use webgraph::graphs::BVGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::*;
use webgraph_algo::prelude::*;

pub fn bench_bfv(c: &mut Criterion) {
    let mut group = c.benchmark_group("Breadth first visit");
    group.sampling_mode(criterion::SamplingMode::Flat);
    group.sample_size(NUM_SAMPLES);
    for (graph_basename, start) in BENCH_GRAPHS {
        let graph = BVGraph::with_basename(graph_basename).load().unwrap();
        let graph_name = std::path::Path::new(graph_basename)
            .file_name()
            .unwrap()
            .to_str()
            .unwrap();
        let input = &graph;
        let parameter = format!("{} ({} nodes)", graph_name, graph.num_nodes());
        group.throughput(Throughput::Elements(graph.num_nodes().try_into().unwrap()));

        group.bench_with_input(
            BenchmarkId::new("Sequential", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    SingleThreadedBreadthFirstVisit::with_start(i, start)
                        .visit(Option::<ProgressLogger>::None)
                        .unwrap()
                });
            },
        );

        group.bench_with_input(BenchmarkId::new("Parallel", &parameter), &input, |b, i| {
            b.iter_with_large_drop(|| {
                ParallelBreadthFirstVisit::with_start(i, start)
                    .visit(Option::<ProgressLogger>::None)
                    .unwrap()
            });
        });
    }
    group.finish();
}
