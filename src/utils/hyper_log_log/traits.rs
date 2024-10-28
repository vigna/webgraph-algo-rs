use crate::prelude::*;
use sux::traits::Word;

pub trait CachableCounter {
    type OwnedCounter;

    fn get_copy(&self) -> Self::OwnedCounter;

    #[inline(always)]
    fn into_owned(self) -> Self::OwnedCounter
    where
        Self: Sized,
    {
        self.get_copy()
    }

    fn copy_into_owned(&self, dst: &mut Self::OwnedCounter) {
        *dst = self.get_copy()
    }
}

pub trait BitwiseCounter<W: Word> {
    fn as_words(&self) -> &[W];

    fn as_mut_words(&mut self) -> &mut [W];

    fn merge_bitwise(&mut self, other: &impl BitwiseCounter<W>);

    #[inline(always)]
    fn set_to_bitwise(&mut self, other: &impl BitwiseCounter<W>) {
        self.set_to_words(other.as_words());
    }

    #[inline(always)]
    fn set_to_words(&mut self, words: &[W]) {
        self.as_mut_words().copy_from_slice(words);
    }
}

pub trait ThreadHelperCounter<'a> {
    /// The type of the thread helper struct.
    type ThreadHelper;

    /// Sets the couter to use the specified thread helper.
    fn use_thread_helper(&mut self, helper: &'a mut Self::ThreadHelper);

    /// Stops the counter from using the thread helper.
    fn remove_thread_helper(&mut self);
}

pub trait HyperLogLog<'a, T, W: Word>:
    Counter<T>
    + ApproximatedCounter<T>
    + CachableCounter
    + BitwiseCounter<W>
    + ThreadHelperCounter<'a>
    + PartialEq
    + Eq
{
}
impl<
        'a,
        T,
        W: Word,
        C: Counter<T>
            + ApproximatedCounter<T>
            + CachableCounter
            + BitwiseCounter<W>
            + ThreadHelperCounter<'a>
            + PartialEq
            + Eq,
    > HyperLogLog<'a, T, W> for C
{
}

pub trait HyperLogLogArray<'a, T, W: Word> {
    type Counter<'b>: HyperLogLog<'a, T, W>
    where
        Self: 'b;

    unsafe fn get_counter_from_shared(&self, index: usize) -> Self::Counter<'_>;

    fn get_counter(&mut self, index: usize) -> Self::Counter<'_> {
        unsafe {
            // Safety: We have a mutable reference so no other references exists
            self.get_counter_from_shared(index)
        }
    }

    fn get_owned_counter(
        &self,
        index: usize,
    ) -> <Self::Counter<'_> as CachableCounter>::OwnedCounter {
        unsafe {
            // Safety: the returned counter is owned, so no shared data exists.
            // Assumption: Counters created with get_counter_from_shared are used
            // correctly
            self.get_counter_from_shared(index).into_owned()
        }
    }

    fn get_thread_helper(&self) -> <Self::Counter<'_> as ThreadHelperCounter<'a>>::ThreadHelper;
}
