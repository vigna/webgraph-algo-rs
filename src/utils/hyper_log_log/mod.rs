mod hyper_log_log_array;
pub use hyper_log_log_array::*;

mod hyper_log_log_counter;
pub use hyper_log_log_counter::*;

mod hyper_log_log_counter2;
pub use hyper_log_log_counter2::*;

pub mod traits;

type HashResult = u64;
