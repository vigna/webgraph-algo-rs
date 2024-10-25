mod hyper_log_log_array;
pub use hyper_log_log_array::*;

mod hyper_log_log_counter;
pub use hyper_log_log_counter::*;

pub mod traits;

type HashResult = u64;

#[cfg(test)]
mod test {
    use super::*;
    use crate::prelude::*;
    use anyhow::Result;

    #[test]
    fn test_counter_creation() -> Result<()> {
        let counters = HyperLogLogCounterArrayBuilder::new()
            .log_2_num_registers(6)
            .build::<usize>(10)?;

        let counter_4 = counters.get_counter(4);

        assert!(counter_4.cached_bits.is_none());
        assert_eq!(counter_4.offset, 2_usize.pow(6) * 4);

        Ok(())
    }

    #[test]
    fn test_counter_edit_inplace() -> Result<()> {
        let counters = HyperLogLogCounterArrayBuilder::new()
            .log_2_num_registers(6)
            .word_type::<u64>()
            .build(10)?;
        let mut counter_4 = counters.get_counter(4);

        counter_4.add(42);

        assert_eq!(counters.residual_mask.count_ones(), 64);
        assert!(counter_4.cached_bits.is_none());
        for i in 0..10 {
            let pointer = counters.bits.as_slice().as_ptr() as *const u64;
            let slice = unsafe {
                let ptr = pointer.add(i * counters.words_per_counter());
                std::slice::from_raw_parts(ptr, counters.words_per_counter())
            };
            if i != 4 {
                assert_eq!(slice, vec![0; counters.words_per_counter()]);
            } else {
                let mut ones = 0;
                for word in slice {
                    ones += word.count_ones();
                }
                assert!(ones > 0);
            }
        }

        Ok(())
    }

    #[test]
    fn test_counter_edit_cached() -> Result<()> {
        let counters = HyperLogLogCounterArrayBuilder::new()
            .log_2_num_registers(6)
            .word_type::<u64>()
            .build(10)?;
        let mut counter_4 = counters.get_counter(4);

        assert!(counter_4.cached_bits.is_none());

        unsafe {
            counter_4.cache();
        }

        assert!(counter_4.cached_bits.is_some());
        assert!(!counter_4.cached_bits.as_ref().unwrap().1);
        assert_eq!(
            counter_4.cached_bits.as_ref().unwrap().0.as_slice(),
            vec![0; counters.words_per_counter()]
        );

        counter_4.add(42);

        assert!(counter_4.cached_bits.as_ref().unwrap().1);
        for i in 0..10 {
            let pointer = counters.bits.as_slice().as_ptr() as *const u64;
            let slice = unsafe {
                let ptr = pointer.add(i * counters.words_per_counter());
                std::slice::from_raw_parts(ptr, counters.words_per_counter())
            };
            assert_eq!(slice, vec![0; counters.words_per_counter()]);
        }

        let mut ones = 0;
        for word in counter_4.cached_bits.as_ref().unwrap().0.as_slice() {
            ones += word.count_ones();
        }
        assert!(ones > 0);

        Ok(())
    }

    #[test]
    fn test_counter_commit_changes() -> Result<()> {
        let counters = HyperLogLogCounterArrayBuilder::new()
            .log_2_num_registers(6)
            .word_type::<u64>()
            .build(10)?;
        let mut counter_4 = counters.get_counter(4);
        unsafe {
            counter_4.cache();
        }
        counter_4.add(42);

        unsafe {
            counter_4.commit_changes(false);
        }

        assert!(counter_4.cached_bits.is_none());
        for i in 0..10 {
            let pointer = counters.bits.as_slice().as_ptr() as *const u64;
            let slice = unsafe {
                let ptr = pointer.add(i * counters.words_per_counter());
                std::slice::from_raw_parts(ptr, counters.words_per_counter())
            };
            if i != 4 {
                assert_eq!(slice, vec![0; counters.words_per_counter()]);
            } else {
                let mut ones = 0;
                for word in slice {
                    ones += word.count_ones();
                }
                assert!(ones > 0);
            }
        }

        Ok(())
    }

    #[test]
    fn test_counter_sync_changes() -> Result<()> {
        let counters = HyperLogLogCounterArrayBuilder::new()
            .log_2_num_registers(6)
            .word_type::<u64>()
            .build(10)?;
        let mut counter_4 = counters.get_counter(4);
        unsafe {
            counter_4.cache();
        }
        counter_4.add(42);

        unsafe {
            counter_4.commit_changes(true);
        }

        assert!(counter_4.cached_bits.is_some());
        assert!(!counter_4.cached_bits.as_ref().unwrap().1);
        for i in 0..10 {
            let pointer = counters.bits.as_slice().as_ptr() as *const u64;
            let slice = unsafe {
                let ptr = pointer.add(i * counters.words_per_counter());
                std::slice::from_raw_parts(ptr, counters.words_per_counter())
            };
            if i != 4 {
                assert_eq!(slice, vec![0; counters.words_per_counter()]);
            } else {
                assert_eq!(slice, counter_4.cached_bits.as_ref().unwrap().0.as_slice())
            }
        }

        Ok(())
    }

    #[test]
    fn test_counter_sync() -> Result<()> {
        let counters = HyperLogLogCounterArrayBuilder::new()
            .log_2_num_registers(6)
            .word_type::<u64>()
            .build(10)?;
        let mut counter_4 = counters.get_counter(4);
        unsafe {
            counter_4.cache();
        }
        counter_4.add(42);

        unsafe {
            counter_4.sync_to_backend();
        }

        assert!(counter_4.cached_bits.is_some());
        assert!(!counter_4.cached_bits.as_ref().unwrap().1);
        for i in 0..10 {
            let pointer = counters.bits.as_slice().as_ptr() as *const u64;
            let slice = unsafe {
                let ptr = pointer.add(i * counters.words_per_counter());
                std::slice::from_raw_parts(ptr, counters.words_per_counter())
            };
            if i != 4 {
                assert_eq!(slice, vec![0; counters.words_per_counter()]);
            } else {
                assert_eq!(slice, counter_4.cached_bits.as_ref().unwrap().0.as_slice())
            }
        }

        Ok(())
    }
}
