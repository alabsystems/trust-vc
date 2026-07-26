//! Regression tests for Seq, Set, Map collection encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Original monolith (727 lines, 34 tests) split for maintainability (#2145).

use super::*;

mod axiom_encoding;
mod cross_width_coercion;
mod filter_range_guard;
mod map_values_range_guard;
mod match_arm_shadowing;
mod precondition_guards;
mod push_and_metadata;
mod set_map_reverse;
