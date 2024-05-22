pub mod argmax;

pub mod argmin;

pub mod mmap_slice;
#[doc(hidden)]
pub use mmap_slice::MmapFlags;
pub use mmap_slice::TempMmapOptions;

mod closure_vec;
pub use closure_vec::closure_vec;
