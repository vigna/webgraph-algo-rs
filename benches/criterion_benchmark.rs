use criterion::{criterion_group, criterion_main};

mod single_benches;

criterion_group!(benches, single_benches::bench_bfv);
criterion_main!(benches);
