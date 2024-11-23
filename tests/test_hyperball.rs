use anyhow::Result;
use common_traits::Float;
use dsi_progress_logger::no_logging;
use epserde::deser::{Deserialize, Flags};
use webgraph::{
    prelude::{BvGraph, DCF},
    traits::SequentialLabeling,
};
use webgraph_algo::{
    algo::hyperball::HyperBallBuilder, threads, utils::hyper_log_log::HyperLogLogBuilder,
};

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

#[test]
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

    let hyper_log_log = HyperLogLogBuilder::<usize>::new(graph.num_nodes())
        .log_2_num_reg(8)
        .seed(42)
        .build()?;
    let bits = hyper_log_log.new_array(
        graph.num_nodes(),
        webgraph_algo::utils::TempMmapOptions::Default,
    )?;
    let result_bits = hyper_log_log.new_array(
        graph.num_nodes(),
        webgraph_algo::utils::TempMmapOptions::Default,
    )?;
    let mut hyperball = HyperBallBuilder::with_transposed(
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
    let actual_closeness_centralities = hyperball.closeness_cetrality()?;
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
