use super::*;
use crate::prelude::*;
use common_traits::{CastableFrom, UpcastableInto};
use std::{borrow::Borrow, hash::*};
use sux::traits::Word;

pub struct HyperLogLogCounter<T, W: Word, H: BuildHasher, L: Borrow<HyperLogLog<T, W, H>>, B> {
    pub(super) logic: L,
    pub(super) backend: B,
    pub(super) _marker: std::marker::PhantomData<(T, W, H)>,
}

impl<
        T: Hash,
        W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>,
        H: BuildHasher,
        L: Borrow<HyperLogLog<T, W, H>>,
        B: AsRef<[W]>,
    > ImmutableCounter<T, HyperLogLog<T, W, H>> for HyperLogLogCounter<T, W, H, L, B>
{
    #[inline(always)]
    fn as_backend(&self) -> &<HyperLogLog<T, W, H> as CounterLogic<T>>::Backend {
        self.backend.as_ref()
    }

    #[inline(always)]
    fn count(&self) -> f64 {
        self.logic.borrow().count(self.backend.as_ref())
    }

    #[inline(always)]
    fn new_helper(&self) -> <HyperLogLog<T, W, H> as CounterLogic<T>>::Helper {
        self.logic.borrow().new_helper()
    }
}

impl<
        T: Hash,
        W: Word + UpcastableInto<HashResult> + CastableFrom<HashResult>,
        H: BuildHasher,
        L: Borrow<HyperLogLog<T, W, H>>,
        B: AsRef<[W]> + AsMut<[W]>,
    > MutableCounter<T, HyperLogLog<T, W, H>> for HyperLogLogCounter<T, W, H, L, B>
{
    #[inline(always)]
    fn add(&mut self, element: T) {
        self.logic.borrow().add(self.backend.as_mut(), element)
    }

    #[inline(always)]
    fn as_mut_backend(&mut self) -> &mut <HyperLogLog<T, W, H> as CounterLogic<T>>::Backend {
        self.backend.as_mut()
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.logic.borrow().clear(self.backend.as_mut())
    }

    #[inline(always)]
    fn merge(&mut self, other: &<HyperLogLog<T, W, H> as CounterLogic<T>>::Backend) {
        self.logic
            .borrow()
            .merge_into(self.backend.as_mut(), other.as_ref())
    }

    #[inline(always)]
    fn merge_with_helper(
        &mut self,
        other: &<HyperLogLog<T, W, H> as CounterLogic<T>>::Backend,
        helper: &mut <HyperLogLog<T, W, H> as CounterLogic<T>>::Helper,
    ) {
        self.logic
            .borrow()
            .merge_into_with_helper(self.backend.as_mut(), other.as_ref(), helper)
    }

    #[inline(always)]
    fn set_to(&mut self, other: &<HyperLogLog<T, W, H> as CounterLogic<T>>::Backend) {
        self.logic
            .borrow()
            .set_to(self.backend.as_mut(), other.as_ref())
    }
}
