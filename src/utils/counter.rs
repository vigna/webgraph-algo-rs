use crate::prelude::*;
use std::{borrow::Borrow, hash::*};
use sux::traits::Word;

pub struct DefaultCounter<
    T,
    W: Word,
    H: BuildHasher,
    C: CounterLogic<T> + MergeCounterLogic<T>,
    L: Borrow<C>,
    B,
> {
    pub(super) logic: L,
    pub(super) backend: B,
    pub(super) _marker: std::marker::PhantomData<(T, W, H, C)>,
}

impl<
        T,
        W: Word,
        H: BuildHasher,
        C: CounterLogic<T> + MergeCounterLogic<T>,
        L: Borrow<C> + Clone,
        B: AsRef<C::Backend> + AsMut<C::Backend>,
    > Counter<T, C> for DefaultCounter<T, W, H, C, L, B>
{
    type OwnedCounter = DefaultCounter<T, W, H, C, L, Box<<C as CounterLogic<T>>::Backend>>;

    #[inline(always)]
    fn as_backend(&self) -> &<C as CounterLogic<T>>::Backend {
        self.backend.as_ref()
    }

    #[inline(always)]
    fn count(&self) -> f64 {
        self.logic.borrow().count(&self.backend)
    }

    #[inline(always)]
    fn new_merge_helper(&self) -> <C as MergeCounterLogic<T>>::MergeHelper {
        self.logic.borrow().new_merge_helper()
    }
    #[inline(always)]
    fn add(&mut self, element: T) {
        self.logic.borrow().add(&mut self.backend, element)
    }

    #[inline(always)]
    fn as_mut_backend(&mut self) -> &mut <C as CounterLogic<T>>::Backend {
        self.backend.as_mut()
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.logic.borrow().clear(&mut self.backend)
    }

    #[inline(always)]
    fn merge(&mut self, other: impl AsRef<C::Backend>) {
        self.logic.borrow().merge_into(&mut self.backend, &other)
    }

    #[inline(always)]
    fn merge_with_helper(
        &mut self,
        other: impl AsRef<C::Backend>,
        helper: &mut <C as MergeCounterLogic<T>>::MergeHelper,
    ) {
        self.logic
            .borrow()
            .merge_into_with_helper(&mut self.backend, &other, helper)
    }

    #[inline(always)]
    fn set_to(&mut self, other: impl AsRef<C::Backend>) {
        self.logic.borrow().set_to(&mut self.backend, &other)
    }

    #[inline(always)]
    fn into_owned(self) -> Self::OwnedCounter {
        todo!()
    }
}
