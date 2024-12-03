use anyhow::Result;
use common_traits::AsBytes;
use common_traits::Float;
use dsi_progress_logger::no_logging;
use epserde::deser::{Deserialize, Flags};
use std::hash::*;
use webgraph::{
    prelude::{BvGraph, DCF},
    traits::SequentialLabeling,
};
use webgraph_algo::utils::SliceCounterArray;
use webgraph_algo::{
    algo::hyperball::HyperBallBuilder, threads, utils::hyper_log_log::HyperLogLogBuilder,
};

/// Jenkins Hasher as implemented in the
/// [Java version](https://github.com/vigna/dsiutils/blob/master/src/it/unimi/dsi/util/HyperLogLogCounterArray.java#L263).
#[derive(Debug, Clone)]
pub struct JenkinsHasher {
    a: u64,
    b: u64,
    c: u64,
    buffer: Vec<u8>,
}

impl JenkinsHasher {
    fn new(seed: u64) -> Self {
        Self {
            a: seed,
            b: seed,
            c: 0x9e3779b97f4a7c13,
            buffer: Vec::with_capacity(u64::BYTES),
        }
    }

    fn digest(&mut self) {
        while self.buffer.len() >= u64::BYTES {
            let bytes = &self.buffer[0..u64::BYTES];
            let word = u64::from_ne_bytes(bytes.try_into().unwrap());
            self.digest_word(word);
            self.buffer.drain(0..u64::BYTES);
        }
    }

    fn digest_word(&mut self, x: u64) {
        // Allow wrapping arithmetics
        let mut a = std::num::Wrapping(self.a);
        let mut b = std::num::Wrapping(self.b);
        let mut c = std::num::Wrapping(self.c);

        // Init state

        a += x;

        // a -= b; a -= c; a ^= (c >>> 43);

        a -= b;
        a -= c;
        a ^= c >> 43;

        // b -= c; b -= a; b ^= (a << 9);

        b -= c;
        b -= a;
        b ^= a << 9;

        // c -= a; c -= b; c ^= (b >>> 8);

        c -= a;
        c -= b;
        c ^= b >> 8;

        // a -= b; a -= c; a ^= (c >>> 38);

        a -= b;
        a -= c;
        a ^= c >> 38;

        // b -= c; b -= a; b ^= (a << 23);

        b -= c;
        b -= a;
        b ^= a << 23;

        // c -= a; c -= b; c ^= (b >>> 5);

        c -= a;
        c -= b;
        c ^= b >> 5;

        // a -= b; a -= c; a ^= (c >>> 35);

        a -= b;
        a -= c;
        a ^= c >> 35;

        // b -= c; b -= a; b ^= (a << 49);

        b -= c;
        b -= a;
        b ^= a << 49;

        // c -= a; c -= b; c ^= (b >>> 11);

        c -= a;
        c -= b;
        c ^= b >> 11;

        // a -= b; a -= c; a ^= (c >>> 12);

        a -= b;
        a -= c;
        a ^= c >> 12;

        // b -= c; b -= a; b ^= (a << 18);

        b -= c;
        b -= a;
        b ^= a << 18;

        // c -= a; c -= b; c ^= (b >>> 22);

        c -= a;
        c -= b;
        c ^= b >> 22;

        // Save modified state

        self.a = a.0;
        self.b = b.0;
        self.c = c.0;
    }
}

impl Hasher for JenkinsHasher {
    fn finish(&self) -> u64 {
        self.c
    }

    fn write(&mut self, bytes: &[u8]) {
        self.buffer.extend_from_slice(bytes);
        if self.buffer.len() >= u64::BYTES {
            self.digest();
        }
    }
}

#[derive(Clone, Debug)]
pub struct JenkinsHasherBuilder {
    seed: u64,
}

impl JenkinsHasherBuilder {
    pub fn new(seed: u64) -> Self {
        Self { seed }
    }
}

impl BuildHasher for JenkinsHasherBuilder {
    type Hasher = JenkinsHasher;

    fn build_hasher(&self) -> Self::Hasher {
        JenkinsHasher::new(self.seed)
    }
}

fn read_float_array(path: impl AsRef<std::path::Path>) -> Result<Vec<f64>> {
    let buffer = std::fs::read(path)?;
    assert!(buffer.len() % 4 == 0);
    let num_floats = buffer.len() / 4;

    let mut int_v = Vec::with_capacity(num_floats);

    unsafe {
        std::ptr::copy_nonoverlapping(
            buffer.as_ptr(),
            int_v.as_mut_ptr() as *mut u8,
            num_floats * 4,
        );
        int_v.set_len(num_floats);
    }

    let mut v = Vec::with_capacity(num_floats);

    for value in int_v {
        v.push(f32::from_be_bytes(value).into());
    }

    Ok(v)
}

fn assert_array_equal<T: Float>(expected: &[T], actual: &[T], threshold: T, name: &str) {
    assert_eq!(expected.len(), actual.len());
    for (i, (&expected, &actual)) in expected.iter().zip(actual).enumerate() {
        let unscaled_difference = (expected - actual).abs();
        let difference = if expected != T::ZERO {
            unscaled_difference / expected
        } else {
            unscaled_difference
        };
        assert!(
            difference < threshold,
            "assertion failed for element {} of {}: {} >= {} (expected: {}, actual: {})",
            i,
            name,
            difference,
            threshold,
            expected,
            actual
        );
    }
}

#[cfg_attr(feature = "slow_tests", test)]
#[cfg_attr(not(feature = "slow_tests"), allow(dead_code))]
fn test_cnr_2000() -> Result<()> {
    let basename = "tests/graphs/cnr-2000";

    let graph = BvGraph::with_basename(basename).load()?;
    let transpose = BvGraph::with_basename(basename.to_owned() + "-t").load()?;
    let cumulative = DCF::load_mmap(basename.to_owned() + ".dcf", Flags::empty())?;

    // These are created using the Java implementation of Hyperball on cnr-2000 with a log2m equal to 8 and seed 42 with Jenkins hash.
    let expected_sum_of_distances =
        read_float_array("./tests/hyperball_results/cnr-2000_sum_of_distances")?;
    let expected_harmonic_centralities =
        read_float_array("./tests/hyperball_results/cnr-2000_harmonic_centrality")?;
    let expected_lin_centralities =
        read_float_array("./tests/hyperball_results/cnr-2000_lin_centrality")?;
    let expected_closeness_centralities =
        read_float_array("./tests/hyperball_results/cnr-2000_closeness_centrality")?;
    let expected_nieminen_centralities =
        read_float_array("./tests/hyperball_results/cnr-2000_nieminen_centrality")?;

    let hyper_log_log = HyperLogLogBuilder::new(graph.num_nodes())
        .log_2_num_reg(8)
        .build_hasher(JenkinsHasherBuilder::new(42))
        .build()?;
    let bits = SliceCounterArray::new(hyper_log_log.clone(), graph.num_nodes())?;
    let result_bits = SliceCounterArray::new(hyper_log_log, graph.num_nodes())?;
    let mut hyperball = HyperBallBuilder::with_transpose(
        &graph,
        &transpose,
        cumulative.as_ref(),
        bits,
        result_bits,
    )
    .sum_of_distances(true)
    .sum_of_inverse_distances(true)
    .build(no_logging![]);

    hyperball.run_until_done(&threads![], no_logging![])?;

    let actual_sum_of_distances = hyperball.sum_of_distances()?;
    let actual_harmonic_cetralities = hyperball.harmonic_centralities()?;
    let actual_lin_centralities = hyperball.lin_centrality()?;
    let actual_closeness_centralities = hyperball.closeness_centrality()?;
    let actual_nieminen_centralities = hyperball.nieminen_centrality()?;

    let threshold = 1e-6;

    // Check that the arrays are equal up to a variation of 0.0001%.
    assert_array_equal(
        &expected_sum_of_distances,
        &actual_sum_of_distances,
        threshold,
        "sum of distances",
    );
    assert_array_equal(
        &expected_harmonic_centralities,
        &actual_harmonic_cetralities,
        threshold,
        "harmonic centralities",
    );
    assert_array_equal(
        &expected_lin_centralities,
        &actual_lin_centralities,
        threshold,
        "lin centralities",
    );
    assert_array_equal(
        &expected_closeness_centralities,
        &actual_closeness_centralities,
        threshold,
        "closeness centralities",
    );
    assert_array_equal(
        &expected_nieminen_centralities,
        &actual_nieminen_centralities,
        threshold,
        "nieminen centralities",
    );

    Ok(())
}
