//! An implementation of the *ExactSumSweep* algorithm.
//!
//! The algorithm has been described by Michele Borassi, Pierluigi Crescenzi,
//! Michel Habib, Walter A. Kosters, Andrea Marino, and Frank W. Takes in “[Fast
//! diameter and radius BFS-based computation in (weakly connected) real-world
//! graphs–With an application to the six degrees of separation
//! games](https://www.sciencedirect.com/science/article/pii/S0304397515001644)”,
//! *Theoretical Computer Science*, 586:59–80, Elsevier, 2015. [DOI
//! 10.1016/j.tcs.2015.02.033](https://doi.org/10.1016/j.tcs.2015.02.033).

mod computer;
mod dir_outputs;
mod output_level;
mod scc_graph;
mod undir_outputs;

/// Module containing all result structures that may be produced as the results
/// of the *ExactSumSweep* algorithm.
pub mod outputs {
    use super::*;

    /// Module containing all result structures that may be produced as the results
    /// of the *ExactSumSweep* algorithm on undirected graphs.
    pub mod undirected {
        pub use super::undir_outputs::*;
    }

    /// Module containing all result structures that may be produced as the results
    /// of the *ExactSumSweep* algorithm on directed graphs.
    pub mod directed {
        pub use super::dir_outputs::*;
    }
}

pub use output_level::*;

use std::cell::UnsafeCell;

pub struct SyncUnsafeSlice<T>(UnsafeCell<*mut [T]>);
unsafe impl<'a, T: Send> Sync for SyncUnsafeSlice<T> {}

impl<T> SyncUnsafeSlice<T> {
    pub fn new(slice: &mut [T]) -> Self {
        Self(UnsafeCell::new(slice as _))
    }

    #[inline(always)]
    pub unsafe fn get_mut_unchecked(&self, index: usize) -> &mut T {
        &mut *(*self.0.get() as *mut T).add(index)
    }

    #[inline(always)]
    pub unsafe fn get_mut(&self, index: usize) -> &mut T {
        let len = (*self.0.get()).len();
        assert!(
            index < len,
            "index out of bounds: the len is {} but the index is {}",
            index,
            len
        );
        self.get_mut_unchecked(index)
    }
}
