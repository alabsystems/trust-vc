//! Collection encoding tests — split into domain submodules.
//!
//! Original monolith (1496 lines, 67 tests) split for maintainability (#2145).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

mod anonymous_receiver;
mod empty_membership;
mod length_and_contains;
mod multiset;
mod seq_operations;
mod set_and_map;

mod typed_anonymous_residuals;
