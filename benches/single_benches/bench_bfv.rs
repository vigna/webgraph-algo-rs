use super::params::*;
use criterion::{BenchmarkId, Criterion, Throughput};
use dsi_progress_logger::ProgressLogger;
use std::convert::Infallible;
use webgraph::prelude::BvGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::visits::breadth_first::*;
use webgraph_algo::algo::visits::{ParVisit, SeqVisit};

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
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = SingleThreadedBreadthFirstVisit::<Infallible, _>::new(g);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .visit(node, |_| Ok(()), &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel (Granularity 1)", &parameter),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParallelBreadthFirstVisit::<Infallible, _>::new(g, 1);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .visit(node, |_| Ok(()), &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel (Granularity 64)", &parameter),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParallelBreadthFirstVisit::<Infallible, _>::new(g, 64);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .visit(node, |_| Ok(()), &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel Fast Callback (Granularity 1)", &parameter),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParallelBreadthFirstVisitFastCB::<Infallible, _>::new(g, 1);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .visit(node, |_| Ok(()), &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel Fast Callback (Granularity 64)", &parameter),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParallelBreadthFirstVisitFastCB::<Infallible, _>::new(g, 1);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .visit(node, |_| Ok(()), &mut Option::<ProgressLogger>::None)
                            .unwrap();
                    }
                });
            },
        );
    }
    group.finish();
}
