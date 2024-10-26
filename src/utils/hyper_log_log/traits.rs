use crate::prelude::*;
use sux::traits::Word;

pub trait CachableCounter: ToOwned {
    #[inline(always)]
    fn get_copy(&self) -> <Self as ToOwned>::Owned {
        self.to_owned()
    }

    #[inline(always)]
    fn into_owned(self) -> <Self as ToOwned>::Owned
    where
        Self: Sized,
    {
        self.to_owned()
    }
}

pub trait BitwiseCounter<T, W: Word> {
    fn as_words(&self) -> &[W];

    unsafe fn as_mut_words_unsafe(&mut self) -> &mut [W];

    unsafe fn merge_bitwise_unsafe(&mut self, other: &impl BitwiseCounter<T, W>);

    #[inline(always)]
    unsafe fn set_to_bitwise_unsafe(&mut self, other: &impl BitwiseCounter<T, W>) {
        self.as_mut_words_unsafe().copy_from_slice(other.as_words());
    }

    #[inline(always)]
    unsafe fn set_to_words_unsafe(&mut self, words: &[W]) {
        self.as_mut_words_unsafe().copy_from_slice(words);
    }
}

pub unsafe trait BitwiseCounterSafe<T, W: Word>: BitwiseCounter<T, W> {
    #[inline(always)]
    fn as_mut_words(&mut self) -> &mut [W] {
        unsafe { self.as_mut_words_unsafe() }
    }

    #[inline(always)]
    fn merge_bitwise(&mut self, other: &impl BitwiseCounter<T, W>) {
        unsafe {
            self.merge_bitwise_unsafe(other);
        }
    }

    #[inline(always)]
    fn set_to_bitwise(&mut self, other: &impl BitwiseCounter<T, W>) {
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

    /// Returns a thread helper for this counter.
    fn get_thread_helper(&self) -> Self::ThreadHelper;
}

pub trait HyperLogLog<'a, T, W: Word>:
    Counter<T>
    + ApproximatedCounter<T>
    + CachableCounter
    + BitwiseCounter<T, W>
    + ThreadHelperCounter<'a>
{
}
impl<
        'a,
        T,
        W: Word,
        C: Counter<T>
            + ApproximatedCounter<T>
            + CachableCounter
            + BitwiseCounter<T, W>
            + ThreadHelperCounter<'a>,
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
    fn get_owned_counter(&'a self, index: usize) -> <Self::Counter as ToOwned>::Owned {
        self.get_counter(index).to_owned()
    }
}
