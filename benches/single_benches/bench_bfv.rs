use super::params::*;
use criterion::{BenchmarkId, Criterion, Throughput};
use dsi_progress_logger::ProgressLogger;
use webgraph::graphs::BVGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::BFV;
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
                    BFV::new_sequential(i)
                        .with_start(start)
                        .build()
                        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
                        .unwrap()
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel (Granularity 1)", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    BFV::new_parallel(i)
                        .with_start(start)
                        .with_granularity(1)
                        .build()
                        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
                        .unwrap()
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel (Granularity 64)", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    BFV::new_parallel(i)
                        .with_start(start)
                        .with_granularity(64)
                        .build()
                        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
                        .unwrap()
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel Fast Callback (Granularity 1)", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    BFV::new_parallel_fast_callback(i)
                        .with_start(start)
                        .with_granularity(1)
                        .build()
                        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
                        .unwrap()
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel Fast Callback (Granularity 64)", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    BFV::new_parallel_fast_callback(i)
                        .with_start(start)
                        .with_granularity(64)
                        .build()
                        .visit(|_, _, _, _| {}, Option::<ProgressLogger>::None)
                        .unwrap()
                });
            },
        );
    }
    group.finish();
}
