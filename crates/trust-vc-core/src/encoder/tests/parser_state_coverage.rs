//! Parser state coverage — facade for concern-split submodules.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from a single 616-line file into three concern-focused submodules
//! per the test-placement policy in `encoder/tests/mod.rs`. Part of #2436.

mod collections;
mod constructor;
mod widths;

use ay_dpll::api::{Logic, Solver};

fn make_solver() -> Solver {
    Solver::try_new(Logic::All).expect("solver construction")
}
