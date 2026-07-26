//! Inductive step verification coverage tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers P1 gaps identified in proof_coverage audit:
//! - Mode 1 (havoc-all) with function context
//! - Mode 2 (frame condition) with loop guard propagation
//! - Mode 2 with multiple variables, mixed modified/unmodified
//! - Mode 2 with function context in the inductive step
//!
//! Original monolith (601 lines, 15 tests) split for maintainability (#2145).
//! Re: #2134

use super::*;

mod collection_and_soundness;
mod inductive_modes;
