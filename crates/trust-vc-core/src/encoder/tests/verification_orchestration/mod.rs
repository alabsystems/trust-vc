//! Targeted tests for verification orchestration modules:
//! - verification/assertion.rs: verify_single_assertion_with_scope
//! - verification/invariants.rs: verify_invariant_inductive_step
//! - verification/mod.rs: verify_legacy (cascading invariants, assert_by accumulation)
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Original monolith (578 lines, 15 tests) split for maintainability (#2145).
//! Re: #2134

use super::*;

mod assertion_coordination;
mod cascading_and_dispatch;
