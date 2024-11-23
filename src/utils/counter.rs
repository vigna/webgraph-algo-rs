use crate::prelude::*;
use std::borrow::Borrow;

pub struct DefaultCounter<L: CounterLogic, B: AsRef<L::Backend> + AsMut<L::Backend>> {
    pub(super) logic: L,
    pub(super) backend: B,
}

impl<L: CounterLogic + Clone, B: AsRef<L::Backend> + AsMut<L::Backend>> Counter<L>
    for DefaultCounter<L, B>
{
    type OwnedCounter = DefaultCounter<L, Box<L::Backend>>;

    fn get_logic(&self) -> &L {
        &self.logic
    }

    #[inline(always)]
    fn as_backend(&self) -> impl AsRef<L::Backend> {
        &self.backend
    }

    #[inline(always)]
    fn count(&self) -> f64 {
        self.logic.count(&self.backend)
    }

    #[inline(always)]
    fn add(&mut self, element: &L::Item) {
        self.logic.add(&mut self.backend, element)
    }

    #[inline(always)]
    fn as_backend_mut(&mut self) -> impl AsMut<L::Backend> {
        &mut self.backend
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.logic.clear(&mut self.backend)
    }

    #[inline(always)]
    fn set_to(&mut self, other: impl AsRef<L::Backend>) {
        self.logic.set_to(&mut self.backend, &other)
    }

    #[inline(always)]
    fn into_owned(self) -> Self::OwnedCounter {
        todo!()
    }
}

impl<L: CounterLogic + MergeCounterLogic + Clone, B: AsRef<L::Backend> + AsMut<L::Backend>>
    MergeCounter<L> for DefaultCounter<L, B>
{
    #[inline(always)]
    fn merge(&mut self, other: impl AsRef<L::Backend>) {
        self.logic.merge(&mut self.backend, &other)
    }

    #[inline(always)]
    fn merge_with_helper(
        &mut self,
        other: impl AsRef<L::Backend>,
        helper: &mut <L as MergeCounterLogic>::Helper,
    ) {
        self.logic
            .merge_with_helper(&mut self.backend, &other, helper)
    }
}
