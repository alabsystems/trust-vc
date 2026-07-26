// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for loop invariant and decreases macros.
//!
//! Verifies that invariant! and loop_decreases! compile, collect obligations,
//! and properly verify through ay.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline
//!
//! NOTE: After #1609 (inductive step via havoc pattern), loop invariants that
//! are not universally valid over all possible variable values are rejected by
//! the inductive step. This is a sound overapproximation: some valid invariants
//! produce false negatives (Counterexample) but no invalid invariants produce
//! false positives (Verified). Non-tautological invariants like `i >= 0` (signed i32)
//! fail because the havoc pattern checks universal validity, not inductiveness.
//! See designs/2026-02-11-loop-invariant-inductive-step.md for details.

use trust_vc::{invariant, loop_decreases};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;

// Import v2 test helpers for proper verification
mod common;

#[path = "loop_invariant_basic/combined_cases.rs"]
mod combined_cases;
#[path = "loop_invariant_basic/decreases_cases.rs"]
mod decreases_cases;
#[path = "loop_invariant_basic/invariant_cases.rs"]
mod invariant_cases;
#[path = "loop_invariant_basic/lexicographic_cases.rs"]
mod lexicographic_cases;
#[path = "loop_invariant_basic/negative_cases.rs"]
mod negative_cases;
