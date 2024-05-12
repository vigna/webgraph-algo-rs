pub mod argmax;

pub mod argmin;

pub mod mmap_slice;
pub use mmap_slice::TempMmapOptions;

mod closure_vec;
pub use closure_vec::closure_vec;
