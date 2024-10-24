use super::params::*;
use criterion::{BenchmarkId, Criterion, Throughput};
use dsi_progress_logger::ProgressLogger;
use webgraph::prelude::BvGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::bfv::BFVBuilder;
use webgraph_algo::prelude::*;

pub fn bench_bfv(c: &mut Criterion) {
    let mut group = c.benchmark_group("Breadth first visit");
    group.sampling_mode(criterion::SamplingMode::Flat);
    group.sample_size(NUM_SAMPLES);
    for &(graph_basename, start) in BENCH_GRAPHS {
        let graph = BvGraph::with_basename(graph_basename).load().unwrap();
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
                    let mut visit = BFVBuilder::new_sequential(i).build();
                    for i in 0..graph.num_nodes() {
                        let node = (i + start) % graph.num_nodes();
                        visit
                            .visit_from_node(|_| {}, node, &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel (Granularity 1)", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    let mut visit = BFVBuilder::new_parallel(i).granularity(1).build();
                    for i in 0..graph.num_nodes() {
                        let node = (i + start) % graph.num_nodes();
                        visit
                            .visit_from_node(|_| {}, node, &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel (Granularity 64)", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    let mut visit = BFVBuilder::new_parallel(i).granularity(64).build();
                    for i in 0..graph.num_nodes() {
                        let node = (i + start) % graph.num_nodes();
                        visit
                            .visit_from_node(|_| {}, node, &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel Fast Callback (Granularity 1)", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    let mut visit = BFVBuilder::new_parallel_fast_callback(i)
                        .granularity(1)
                        .build();
                    for i in 0..graph.num_nodes() {
                        let node = (i + start) % graph.num_nodes();
                        visit
                            .visit_from_node(|_| {}, node, &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel Fast Callback (Granularity 64)", &parameter),
            &input,
            |b, i| {
                b.iter_with_large_drop(|| {
                    let mut visit = BFVBuilder::new_parallel_fast_callback(i)
                        .granularity(64)
                        .build();
                    for i in 0..graph.num_nodes() {
                        let node = (i + start) % graph.num_nodes();
                        visit
                            .visit_from_node(|_| {}, node, &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );
    }
    group.finish();
}
