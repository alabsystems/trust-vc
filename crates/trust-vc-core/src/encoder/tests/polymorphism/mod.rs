// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Tests for Poly/Box/Unbox type-erasure encoding (#2053).

use super::result_oracles::{expect_counterexample, expect_verified};
use crate::encoder::polymorphism::PolyContext;
use crate::ir::TrustVcType;
use ay_dpll::api::{Logic, Solver, Sort};

mod basic_box_unbox;
mod end_to_end;
mod full_pipeline;
mod solver_diagnostics;

/// Helper: create a solver for polymorphism tests.
fn test_solver() -> Solver {
    Solver::try_new(Logic::All).expect("invariant: Logic::All should construct a solver")
}
