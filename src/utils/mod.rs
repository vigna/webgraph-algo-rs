mod argmax;
mod argmin;

/// Module containing mathematical utilities.
pub mod math {
    pub use super::argmax::*;
    pub use super::argmin::*;
}

mod mmap_slice;
#[doc(hidden)]
pub use mmap_slice::MmapFlags;
pub use mmap_slice::{MmapSlice, TempMmapOptions};

mod closure_vec;
pub use closure_vec::closure_vec;

mod hyper_log_log;

pub mod traits;
