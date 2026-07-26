// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Comprehensive soundness test suite
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid code
//!
//! This test suite is critical for ensuring the verification system is sound.
//! Each test MUST produce a counterexample or Unknown result for invalid code.
//! If any of these tests produce Verified, we have a soundness bug.

use trust_vc::assert_by;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
// ============================================================================
// Integer Overflow Tests
// ============================================================================

mod common;

#[test]
fn test_soundness_u32_overflow_constant_folded() {
    common::with_clean_verification(|| {
        // wrapping_add evaluates at Rust runtime before ay sees it.
        // u32::MAX.wrapping_add(1) == 0 evaluates to `true` at runtime,
        // so assert_by! collects "true" which trivially verifies.
        // To test overflow soundness, use symbolic variables (not literals).
        assert_by!(u32::MAX.wrapping_add(1) == 0);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Constant-folded `true` correctly verifies
        assert!(
            matches!(result, VerifyResult::Verified),
            "Constant-folded true should verify, got: {:?}",
            result
        );
    })
}

#[test]
fn test_soundness_i32_overflow_constant_folded() {
    common::with_clean_verification(|| {
        // wrapping_add evaluates at Rust runtime before ay sees it.
        // i32::MAX.wrapping_add(1) == i32::MIN evaluates to `true`.
        assert_by!(i32::MAX.wrapping_add(1) == i32::MIN);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Constant-folded `true` correctly verifies
        assert!(
            matches!(result, VerifyResult::Verified),
            "Constant-folded true should verify, got: {:?}",
            result
        );
    })
}

// ============================================================================
// False Division Assertion Tests
// ============================================================================

#[test]
fn test_soundness_false_division_assertion_fails() {
    common::with_clean_verification(|| {
        // Test that an incorrect quotient is rejected.
        // 10/2 == 5, not 3 — the assertion is false.
        let x = 10i32;
        let y = 2i32;

        assert_by!(x / y == 3);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should NOT verify - the assertion is false
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: False division assertion was verified as correct!"
        );
    })
}

// ============================================================================
// Division/Modulo by Zero Tests (#1734)
// ============================================================================
// These tests use VerificationContext directly because assert_by! evaluates
// the expression at runtime, which panics on division by zero before
// verification can run. The encoder catches div/mod-by-zero via overflow
// checks when the divisor is a variable that could be zero.

#[test]
fn test_soundness_div_by_zero_fails() {
    // Division by an unconstrained variable must NOT verify — the variable
    // could be zero, and Rust division by zero is undefined behavior.
    let mut ctx = trust_vc_core::vc::VerificationContext::new().with_overflow_checks();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");
    ctx.push_assume("x_val", "x == 10");
    // y is unconstrained — could be 0
    ctx.push_assert("div_result", "x / y >= 0");

    let result = ctx.verify();
    assert!(
        !matches!(result, VerifyResult::Verified),
        "SOUNDNESS BUG: Division by unconstrained variable (could be zero) was verified!"
    );
}

#[test]
fn test_soundness_mod_by_zero_fails() {
    // Modulo by an unconstrained variable must NOT verify — the variable
    // could be zero, and Rust modulo by zero is undefined behavior.
    let mut ctx = trust_vc_core::vc::VerificationContext::new().with_overflow_checks();
    ctx.declare_var_parsed("x", "u32");
    ctx.declare_var_parsed("y", "u32");
    ctx.push_assume("x_val", "x == 17");
    // y is unconstrained — could be 0
    ctx.push_assert("mod_result", "x % y == 2");

    let result = ctx.verify();
    assert!(
        !matches!(result, VerifyResult::Verified),
        "SOUNDNESS BUG: Modulo by unconstrained variable (could be zero) was verified!"
    );
}

// ============================================================================
// Type System Soundness Tests
// ============================================================================

#[test]
fn test_soundness_type_confusion_fails() {
    common::with_clean_verification(|| {
        // Type confusion should fail
        // In a sound system, we can't prove that an i32 equals a u32 with different bit patterns
        let x: i32 = -1;
        let y: u32 = u32::MAX;

        // This comparison is nonsensical and should fail
        assert_by!(x as u32 == y && x >= 0); // -1 is not >= 0

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should NOT verify
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: Type confusion was verified as correct!"
        );
    })
}

// ============================================================================
// Contract Violation Tests
// ============================================================================

// Contract violation tests are in test_obligation_soundness.rs,
// contracts_negative.rs, and test_requires_soundness_bug_1399.rs.

// ============================================================================
// Loop Invariant Soundness Tests
// ============================================================================

// Loop invariant soundness tests are in loop_invariant_negative.rs (6 tests)
// and test_comprehensive_negative_verification.rs.

// ============================================================================
// Termination Soundness Tests
// ============================================================================

// Termination soundness tests blocked on full decreases verification (#1353).

// ============================================================================
// Arithmetic Soundness Tests
// ============================================================================

#[test]
fn test_soundness_impossible_equation_fails() {
    common::with_clean_verification(|| {
        // 2 + 2 = 5 should never verify
        assert_by!(2 + 2 == 5);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should NOT verify
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: 2 + 2 = 5 was verified as correct!"
        );
    })
}

#[test]
fn test_soundness_contradiction_fails() {
    common::with_clean_verification(|| {
        // Use variables to avoid clippy impossible_comparisons warning
        // We're intentionally testing that contradictions are caught
        let lower = 10;
        let upper = 3;
        let x = 5;
        assert_by!(x > lower && x < upper); // Impossible: x > 10 AND x < 3

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should NOT verify
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: Contradictory assertions were verified!"
        );
    })
}

// ============================================================================
// Memory Safety Soundness Tests
// ============================================================================

#[test]
fn test_soundness_array_bounds_fails() {
    common::with_clean_verification(|| {
        let arr = [1, 2, 3, 4, 5];
        let index = 10; // Out of bounds

        // This should fail - array access out of bounds
        assert_by!(arr.get(index).is_some());

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Should NOT verify
        assert!(
            !matches!(result, VerifyResult::Verified),
            "SOUNDNESS BUG: Out-of-bounds array access was verified!"
        );
    })
}

// ============================================================================
// Test Helper Functions
// ============================================================================

// Unused helpers removed to satisfy clippy dead_code warnings.
