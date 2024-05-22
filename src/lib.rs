pub mod algo;
pub mod utils;

pub mod prelude {
    pub use crate::algo::traits::*;
    #[doc(hidden)]
    pub use crate::utils::MmapFlags;
    pub use crate::utils::TempMmapOptions;
}
