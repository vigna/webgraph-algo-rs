mod hyper_log_log_array;
pub use hyper_log_log_array::*;

mod hyper_log_log_counter;
pub use hyper_log_log_counter::*;

mod bitwise_utils;
use bitwise_utils::*;

/// The type returned by the hash function.
type HashResult = u64;
