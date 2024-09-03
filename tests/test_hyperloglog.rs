use anyhow::Result;
use webgraph_algo::{prelude::Counter, utils::HyperLogLogCounterArray};

#[test]
fn test_single() -> Result<()> {
    let num_trials = 10;
    let sizes = [1, 10, 100, 1000, 100_000];
    let log2ms = [6, 8, 12];

    for size in sizes {
        for log2m in log2ms {
            let rsd = HyperLogLogCounterArray::relative_standard_deviation(log2m);
            let mut correct = 0;

            for _ in 0..num_trials {
                let counters = HyperLogLogCounterArray::from_log_2_num_registers(1, size, log2m);
                let mut counter = counters.get_counter(0);
                let incr = 1 << 32 / size;
                let mut x = i64::MIN;
                for _ in 0..size {
                    counter.add(x);
                    x += incr;
                }

                let float_rsd = rsd as f64;
                let float_size = size as f64;
                let float_count = counter.count() as f64;

                if (float_size - float_count).abs() / float_size < 2.0 * float_rsd {
                    correct += 1;
                }
            }

            assert!(correct >= 9);
        }
    }

    Ok(())
}
