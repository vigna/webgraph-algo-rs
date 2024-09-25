use crate::{
    prelude::*,
    utils::{HyperLogLogCounter, HyperLogLogCounterArray, HyperLogLogCounterArrayBuilder},
};
use common_traits::IntoAtomic;
use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
use sux::traits::Word;
use webgraph::traits::RandomAccessGraph;

pub struct HyperBall<
    'a,
    G1: RandomAccessGraph,
    G2: RandomAccessGraph,
    W: Word + IntoAtomic = usize,
    H: BuildHasher = BuildHasherDefault<DefaultHasher>,
> {
    /// The direct graph to analyze
    graph: &'a G1,
    /// The transposed of the graph to analyze
    rev_graph: Option<&'a G2>,
    /// The current status of Hyperball
    current: HyperLogLogCounterArray<G1::Label, W, H>,
    /// The new status of Hyperball after an iteration
    new: HyperLogLogCounterArray<G1::Label, W, H>,
}

impl<'a, G1: RandomAccessGraph, G2: RandomAccessGraph, W: Word + IntoAtomic, H: BuildHasher>
    HyperBall<'a, G1, G2, W, H>
{
    /// Swaps the undelying backend [`HyperLogLogCounterArray`] between old and current and returs self.
    #[inline(always)]
    fn swap_backend(&mut self) {
        std::mem::swap(&mut self.current, &mut self.new)
    }

    /// Returns the counter of the specified index using as backend [`Self::current`].
    #[inline(always)]
    fn get_current_counter(&self, index: usize) -> HyperLogLogCounter<G1::Label, W, H> {
        self.current.get_counter(index)
    }

    /// Returns the counter of the specified index using as backend [`Self::new`].
    #[inline(always)]
    fn get_new_counter(&self, index: usize) -> HyperLogLogCounter<G1::Label, W, H> {
        self.new.get_counter(index)
    }
}
