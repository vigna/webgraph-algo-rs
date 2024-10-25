use super::*;
use crate::prelude::*;

pub trait CounterArray<T> {
    type Counter<'a>
    where
        Self: 'a;

    fn get_counter<'a>(&'a self, index: usize) -> Self::Counter<'a>;
}
