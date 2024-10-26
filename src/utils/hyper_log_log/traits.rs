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

    unsafe fn as_mut_words_unsafe(&mut self) -> &mut [W];

    unsafe fn merge_bitwise_unsafe(&mut self, other: &impl BitwiseCounter<W>);

    #[inline(always)]
    unsafe fn set_to_bitwise_unsafe(&mut self, other: &impl BitwiseCounter<W>) {
        self.set_to_words_unsafe(other.as_words());
    }

    #[inline(always)]
    unsafe fn set_to_words_unsafe(&mut self, words: &[W]) {
        self.as_mut_words_unsafe().copy_from_slice(words);
    }
}

pub unsafe trait BitwiseCounterSafe<W: Word>: BitwiseCounter<W> {
    #[inline(always)]
    fn as_mut_words(&mut self) -> &mut [W] {
        unsafe { self.as_mut_words_unsafe() }
    }

    #[inline(always)]
    fn merge_bitwise(&mut self, other: &impl BitwiseCounter<W>) {
        unsafe {
            self.merge_bitwise_unsafe(other);
        }
    }

    #[inline(always)]
    fn set_to_bitwise(&mut self, other: &impl BitwiseCounter<W>) {
        unsafe {
            self.set_to_bitwise_unsafe(other);
        }
    }

    #[inline(always)]
    fn set_to_words(&mut self, words: &[W]) {
        unsafe {
            self.set_to_words_unsafe(words);
        }
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

pub trait CounterArray<'a> {
    type Counter;

    fn get_counter(&'a self, index: usize) -> Self::Counter;
}

pub trait CachableCounterArray<'a>: CounterArray<'a>
where
    <Self as CounterArray<'a>>::Counter: CachableCounter,
{
    #[inline(always)]
    fn get_owned_counter(
        &'a self,
        index: usize,
    ) -> <Self::Counter as CachableCounter>::OwnedCounter {
        self.get_counter(index).into_owned()
    }
}

pub trait ThreadHelperCounterArray<'a>: CounterArray<'a>
where
    Self::Counter: ThreadHelperCounter<'a>,
{
    fn get_thread_helper(&self) -> <Self::Counter as ThreadHelperCounter<'a>>::ThreadHelper;
}

pub trait HyperLogLogArray<'a>:
    CounterArray<'a> + CachableCounterArray<'a> + ThreadHelperCounterArray<'a>
where
    <Self as CounterArray<'a>>::Counter: CachableCounter + ThreadHelperCounter<'a>,
{
}

impl<'a, T: CounterArray<'a> + CachableCounterArray<'a> + ThreadHelperCounterArray<'a>>
    HyperLogLogArray<'a> for T
where
    T::Counter: CachableCounter + ThreadHelperCounter<'a>,
{
}
