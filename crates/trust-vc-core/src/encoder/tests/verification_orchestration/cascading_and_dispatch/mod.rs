//! Cascading loop invariants, assert-by conclusion cascading, solver mode
//! dispatch, and frame condition invariant tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from verification_orchestration/mod.rs (#2145).

use super::*;

mod compute_mode;
mod invariants_and_assert_by;
mod solver_modes;
