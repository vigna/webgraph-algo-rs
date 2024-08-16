use crate::prelude::*;
use std::marker::PhantomData;

pub struct HyperLogLogCounter<T> {
    _phantom_data: PhantomData<T>,
}

impl<T> HyperLogLogCounter<T> {}

impl<T> Counter<T> for HyperLogLogCounter<T> {
    fn add(&mut self, element: T) {
        todo!()
    }

    fn count(&self) -> u64 {
        todo!()
    }

    fn clear(&mut self) {
        todo!()
    }
}

impl<T> ApproximatedCounter<T> for HyperLogLogCounter<T> {}
