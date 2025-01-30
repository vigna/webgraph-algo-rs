/*
 * SPDX-FileCopyrightText: 2024 Matteo Dell'Acqua
 * SPDX-FileCopyrightText: 2025 Sebastiano Vigna
 *
 * SPDX-License-Identifier: Apache-2.0 OR LGPL-2.1-or-later
 */

mod hyper_log_log_logic;
pub use hyper_log_log_logic::*;

/// The type returned by the hash function.
type HashResult = u64;
