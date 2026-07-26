//! Advanced verification tests — quantifiers, functions, broadcast, and type bounds.
//!
//! Split from monolithic `advanced.rs` (1,599 lines, 74 tests) into domain
//! submodules for maintainability (#2145).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

mod broadcast;
mod broadcast_mode;
mod function_calls;
mod match_arm_shadowing;
mod quantifier_arithmetic;
mod quantifier_bounds;
mod type_bounds;
