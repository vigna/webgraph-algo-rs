use crate::prelude::*;
use std::borrow::Borrow;

pub struct DefaultCounter<L: CounterLogic, B> {
    pub(super) logic: L,
    pub(super) backend: B,
}

impl<L: CounterLogic + Clone, B: AsRef<L::Backend>> Counter<L> for DefaultCounter<L, B> {
    type OwnedCounter = DefaultCounter<L, Box<L::Backend>>;

    fn get_logic(&self) -> &L {
        &self.logic
    }

    #[inline(always)]
    fn as_backend(&self) -> &L::Backend {
        self.backend.as_ref()
    }

    #[inline(always)]
    fn count(&self) -> f64 {
        self.logic.count(self.backend.as_ref())
    }
    #[inline(always)]
    fn into_owned(self) -> Self::OwnedCounter {
        todo!()
    }
}

impl<L: CounterLogic + Clone, B: AsRef<L::Backend> + AsMut<L::Backend>> CounterMut<L>
    for DefaultCounter<L, B>
{
    #[inline(always)]
    fn add(&mut self, element: impl Borrow<L::Item>) {
        self.logic.add(self.backend.as_mut(), element)
    }

    #[inline(always)]
    fn as_backend_mut(&mut self) -> &mut L::Backend {
        self.backend.as_mut()
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.logic.clear(self.backend.as_mut())
    }

    #[inline(always)]
    fn set(&mut self, other: &L::Backend) {
        self.logic.set(self.backend.as_mut(), other)
    }
}

impl<L: CounterLogic + MergeCounterLogic + Clone, B: AsRef<L::Backend> + AsMut<L::Backend>>
    MergeCounter<L> for DefaultCounter<L, B>
{
    #[inline(always)]
    fn merge(&mut self, other: &L::Backend) {
        self.logic.merge(self.backend.as_mut(), other)
    }

    #[inline(always)]
    fn merge_with_helper(
        &mut self,
        other: &L::Backend,
        helper: &mut <L as MergeCounterLogic>::Helper,
    ) {
        self.logic
            .merge_with_helper(self.backend.as_mut(), other, helper)
    }
}
