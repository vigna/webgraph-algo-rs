mod slice_counter_array;
pub use slice_counter_array::*;

mod hyper_log_log_logic;
pub use hyper_log_log_logic::*;

mod bitwise_utils;
use bitwise_utils::*;

/// The type returned by the hash function.
type HashResult = u64;
