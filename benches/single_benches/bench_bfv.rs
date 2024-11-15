use super::params::*;
use criterion::{BenchmarkId, Criterion, Throughput};
use dsi_progress_logger::prelude::*;
use unwrap_infallible::UnwrapInfallible;
use webgraph::prelude::BvGraph;
use webgraph::traits::SequentialLabeling;
use webgraph_algo::algo::visits::breadth_first::*;
use webgraph_algo::algo::visits::{Parallel, Sequential};
use webgraph_algo::threads;

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
                    let mut visit = Seq::new(g);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .visit(node, |_| Ok(()), no_logging![])
                            .unwrap_infallible();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel fair no predecessors (Granularity 1)", &parameter),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParFair::new(g, 1);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .par_visit(node, |_| Ok(()), &threads![], no_logging![])
                            .unwrap_infallible();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel fair no predecessors (Granularity 64)", &parameter),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParFair::new(g, 64);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .par_visit(node, |_| Ok(()), &threads![], no_logging![])
                            .unwrap_infallible();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new(
                "Parallel fair with predecessors (Granularity 1)",
                &parameter,
            ),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParFairPred::new(g, 1);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .par_visit(node, |_| Ok(()), &threads![], no_logging![])
                            .unwrap_infallible();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new(
                "Parallel fair with predecessors (Granularity 64)",
                &parameter,
            ),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParFairPred::new(g, 64);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .par_visit(node, |_| Ok(()), &threads![], no_logging![])
                            .unwrap_infallible();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel Fast Callback (Granularity 1)", &parameter),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParLowMem::new(g, 1);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .par_visit(node, |_| Ok(()), &threads![], no_logging![])
                            .unwrap_infallible();
                    }
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("Parallel Fast Callback (Granularity 64)", &parameter),
            &input,
            |b, g| {
                b.iter_with_large_drop(|| {
                    let mut visit = ParLowMem::new(g, 1);
                    for i in 0..g.num_nodes() {
                        let node = (i + start) % g.num_nodes();
                        visit
                            .par_visit(node, |_| Ok(()), &threads![], no_logging![])
                            .unwrap_infallible();
                    }
                });
            },
        );
    }
    group.finish();
}
