use super::*;
use crate::prelude::*;

pub trait CounterArray<'a> {
    type Counter;

    fn get_counter(&'a self, index: usize) -> Self::Counter;
}

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

pub trait CachableCounterArray<'a>: CounterArray<'a>
where
    <Self as CounterArray<'a>>::Counter: CachableCounter,
{
    #[inline(always)]
    fn get_owned_counter(&'a self, index: usize) -> <Self::Counter as ToOwned>::Owned {
        self.get_counter(index).to_owned()
    }
}
