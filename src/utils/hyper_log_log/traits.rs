use super::*;
use crate::prelude::*;

pub trait CounterArray {
    type Counter<'a>
    where
        Self: 'a;

    fn get_counter<'a>(&'a self, index: usize) -> Self::Counter<'a>;
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

pub trait CachableCounterArray: CounterArray
where
    for<'a> <Self as CounterArray>::Counter<'a>: CachableCounter,
{
    #[inline(always)]
    fn get_owned_counter<'a>(&'a self, index: usize) -> <Self::Counter<'a> as ToOwned>::Owned {
        self.get_counter(index).to_owned()
    }
}
