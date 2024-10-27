mod hyper_log_log_array;
pub use hyper_log_log_array::*;

mod hyper_log_log_counter;
pub use hyper_log_log_counter::*;

pub mod traits;

mod bitwise_utils;
use bitwise_utils::*;

type HashResult = u64;
