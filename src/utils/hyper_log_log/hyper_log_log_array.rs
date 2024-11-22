use super::*;
use crate::{prelude::*, utils::MmapSlice};
use common_traits::{Atomic, CastableFrom, IntoAtomic, UpcastableInto};
use std::hash::*;
use sux::traits::Word;

pub struct HyperLogLogArray<
    T,
    W: Word + IntoAtomic,
    H: BuildHasher = BuildHasherDefault<DefaultHasher>,
> {
    logic: HyperLogLog<T, W, H>,
    backend: MmapSlice<W::AtomicType>,
    len: usize,
}

impl<T, W: Word + IntoAtomic, H: BuildHasher> HyperLogLogArray<T, W, H> {
    ///Returns the number of elements in the array, also referred to as its ‘length’.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the array contains no elements.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<
        T: Hash,
        W: Word + IntoAtomic + UpcastableInto<HashResult> + CastableFrom<HashResult>,
        H: BuildHasher + Clone,
    > CounterArray<T, HyperLogLog<T, W, H>> for HyperLogLogArray<T, W, H>
{
    type SharedCounter<'a> = HyperLogLogCounter<T, W, H, &'a HyperLogLog<T,W, H>, &'a [W]> where T: 'a, W: 'a, H: 'a;
    type MutCounter<'a> = HyperLogLogCounter<T, W, H, &'a HyperLogLog<T,W, H>, &'a mut [W]> where T: 'a, W: 'a, H: 'a;
    type OwnedCounter = HyperLogLogCounter<T, W, H, HyperLogLog<T, W, H>, Box<[W]>>;

    fn get_backend(&self, index: usize) -> &<HyperLogLog<T, W, H> as CounterLogic<T>>::Backend {
        let offset = index * self.logic.words_per_counter();
        let mut ptr = self.backend.as_ptr() as *const W;

        unsafe {
            ptr = ptr.add(offset);
        }

        unsafe { std::slice::from_raw_parts(ptr, self.logic.words_per_counter()) }
    }

    unsafe fn get_backend_mut_unsafe(
        &self,
        index: usize,
    ) -> &mut <HyperLogLog<T, W, H> as CounterLogic<T>>::Backend {
        let offset = index * self.logic.words_per_counter();
        let mut ptr = self.backend.as_ptr() as *const W as *mut W;

        unsafe {
            ptr = ptr.add(offset);
        }

        unsafe {
            // Safety:
            // * data is valid for both reads and writes for `len * mem::size_of::<W>()`,
            //   the entire range is a single allocated object and is non-null and aligned
            //   as the pointer was obtained from an already existing slice.
            // * data points to `len` consecutive initialized values of W
            // * The caller guarantees that the memory referenced by the returned slice
            //   will not be accessed through any other pointer for the lifetime of the slice
            // * The total size of the slice is not larger than `isize::MAX`
            std::slice::from_raw_parts_mut(ptr, self.logic.words_per_counter())
        }
    }

    #[inline(always)]
    fn get_counter_logic(&self) -> &HyperLogLog<T, W, H> {
        &self.logic
    }

    fn get_counter(&self, index: usize) -> Self::SharedCounter<'_> {
        let bits = self.get_backend(index);
        Self::SharedCounter {
            logic: &self.logic,
            backend: bits,
            _marker: std::marker::PhantomData,
        }
    }

    unsafe fn get_mut_counter_unsafe(&self, index: usize) -> Self::MutCounter<'_> {
        let bits = self.get_backend_mut_unsafe(index);
        Self::MutCounter {
            logic: &self.logic,
            backend: bits,
            _marker: std::marker::PhantomData,
        }
    }

    fn get_owned_counter(&self, index: usize) -> Self::OwnedCounter {
        let bits = self.get_backend(index).into();
        Self::OwnedCounter {
            logic: self.logic.clone(),
            backend: bits,
            _marker: std::marker::PhantomData,
        }
    }

    fn clear(&mut self) {
        self.backend.fill_with(|| W::AtomicType::new(W::ZERO));
    }
}
