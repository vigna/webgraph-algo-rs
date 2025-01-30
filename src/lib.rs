/*
 * SPDX-FileCopyrightText: 2024 Matteo Dell'Acqua
 * SPDX-FileCopyrightText: 2025 Sebastiano Vigna
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

pub mod algo;
pub mod utils;

/// Module exposing all traits in a single level.
pub mod traits {
    use super::*;
    pub use algo::traits::*;
    pub use utils::traits::*;
}

/// Use `use webgraph_algo::prelude::*;` to import common utilities, modules and
/// all traits.
pub mod prelude {
    use super::*;
    pub use algo::exact_sum_sweep;
    pub use algo::hyperball;
    pub use algo::sccs;
    pub use algo::visits::breadth_first;
    pub use algo::visits::depth_first;
    pub use traits::*;
    #[doc(hidden)]
    pub use utils::MmapFlags;
    pub use utils::TempMmapOptions;
}
