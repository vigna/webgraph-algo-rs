mod hyper_log_log_array;
pub use hyper_log_log_array::*;

mod hyper_log_log_counter;
pub use hyper_log_log_counter::*;

mod hyper_log_log_counter2;
pub use hyper_log_log_counter2::*;

pub mod traits;

type HashResult = u64;

pub(crate) trait WordHash:
    sux::traits::Word
    + common_traits::IntoAtomic
    + TryFrom<HashResult>
    + common_traits::UpcastableInto<HashResult>
{
}
impl<
        T: sux::traits::Word
            + common_traits::IntoAtomic
            + TryFrom<HashResult>
            + common_traits::UpcastableInto<HashResult>,
    > WordHash for T
{
}
