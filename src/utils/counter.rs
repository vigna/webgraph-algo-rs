use crate::prelude::*;
use std::borrow::Borrow;

pub struct DefaultCounter<L: CounterLogic, BL: Borrow<L>, B> {
    logic: BL,
    backend: B,
    _marker: std::marker::PhantomData<L>,
}

impl<L: CounterLogic, BL: Borrow<L>, B> DefaultCounter<L, BL, B> {
    pub fn new(logic: BL, backend: B) -> Self {
        Self {
            logic,
            backend,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<L: CounterLogic + Clone, BL: Borrow<L>, B: AsRef<L::Backend>> Counter<L>
    for DefaultCounter<L, BL, B>
{
    type OwnedCounter = DefaultCounter<L, L, Box<L::Backend>>;

    fn get_logic(&self) -> &L {
        self.logic.borrow()
    }

    #[inline(always)]
    fn as_backend(&self) -> &L::Backend {
        self.backend.as_ref()
    }

    #[inline(always)]
    fn count(&self) -> f64 {
        self.logic.borrow().count(self.backend.as_ref())
    }
    #[inline(always)]
    fn into_owned(self) -> Self::OwnedCounter {
        todo!()
    }
}

impl<L: CounterLogic + Clone, BL: Borrow<L>, B: AsRef<L::Backend> + AsMut<L::Backend>> CounterMut<L>
    for DefaultCounter<L, BL, B>
{
    #[inline(always)]
    fn add(&mut self, element: impl Borrow<L::Item>) {
        self.logic.borrow().add(self.backend.as_mut(), element)
    }

    #[inline(always)]
    fn as_backend_mut(&mut self) -> &mut L::Backend {
        self.backend.as_mut()
    }

    #[inline(always)]
    fn clear(&mut self) {
        self.logic.borrow().clear(self.backend.as_mut())
    }

    #[inline(always)]
    fn set(&mut self, other: &L::Backend) {
        self.logic.borrow().set(self.backend.as_mut(), other)
    }
}

impl<
        L: CounterLogic + MergeCounterLogic + Clone,
        BL: Borrow<L>,
        B: AsRef<L::Backend> + AsMut<L::Backend>,
    > MergeCounter<L> for DefaultCounter<L, BL, B>
{
    #[inline(always)]
    fn merge(&mut self, other: &L::Backend) {
        self.logic.borrow().merge(self.backend.as_mut(), other)
    }

    #[inline(always)]
    fn merge_with_helper(
        &mut self,
        other: &L::Backend,
        helper: &mut <L as MergeCounterLogic>::Helper,
    ) {
        self.logic
            .borrow()
            .merge_with_helper(self.backend.as_mut(), other, helper)
    }
}
