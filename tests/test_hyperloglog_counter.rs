use anyhow::Result;
use webgraph_algo::{prelude::*, utils::HyperLogLogCounterArray};

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
                let counters = HyperLogLogCounterArray::with_log_2_num_registers(1, size, log2m);
                let mut counter = counters.get_counter(0);
                let incr = (1 << 32) / size as i64;
                let mut x = i64::MIN;
                for _ in 0..size {
                    counter.add(x);
                    x += incr;
                }

                let float_size = size as f64;

                if (float_size - counter.estimate_count()).abs() / float_size < 2.0 * rsd {
                    correct += 1;
                }
            }

            assert!(correct >= 9);
        }
    }

    Ok(())
}

#[test]
fn test_double() -> Result<()> {
    let num_trials = 10;
    let sizes = [1, 10, 100, 1000, 100_000];
    let log2ms = [4, 6, 8, 12];

    for size in sizes {
        for log2m in log2ms {
            let rsd = HyperLogLogCounterArray::relative_standard_deviation(log2m);
            let mut correct_0 = 0;
            let mut correct_1 = 0;

            for _ in 0..num_trials {
                let counters = HyperLogLogCounterArray::with_log_2_num_registers(2, size, log2m);
                let incr = (1 << 32) / size as i64;
                let mut x = i64::MIN;
                for _ in 0..size {
                    counters.get_counter(0).add(x);
                    counters.get_counter(1).add(x);
                    x += incr;
                }

                let float_size = size as f64;

                if (float_size - counters.get_counter(0).estimate_count()).abs() / float_size
                    < 2.0 * rsd
                {
                    correct_0 += 1;
                }
                if (float_size - counters.get_counter(1).estimate_count()).abs() / float_size
                    < 2.0 * rsd
                {
                    correct_1 += 1;
                }
            }

            assert!(correct_0 >= 9);
            assert!(correct_1 >= 9);
        }
    }

    Ok(())
}
