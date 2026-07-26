// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for solver hook macros: assert_by_nonlinear!, assert_by_bit_vector!, assert_by_compute!
//!
//! All tests invoke ay verification through VerificationPipeline and check
//! specific outcomes. Tests with variables exercise the runtime variable
//! registration added in #1596 (collect_variable_runtime).
//!
//! STATUS:
//! - All three solver modes (nonlinear, bit_vector, compute) now produce real
//!   results: concrete true claims → Verified, concrete false claims →
//!   Counterexample, unresolved symbolic residue → Unknown.
//! - `assert_by_compute!` performs bounded proof-by-computation (#2454).
//! - `assert_by_nonlinear!` uses ay's NIA theory; `assert_by_bit_vector!`
//!   uses ay's BV theory. Both fully functional since #2463.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc::{assert_by_bit_vector, assert_by_compute, assert_by_nonlinear};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

fn verify_expect_verified(context: &str) {
    let result = VerificationPipeline::collect_from_macros().verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "{context}: Expected Verified, got {result:?}",
    );
}

fn verify_expect_counterexample(context: &str) {
    let result = VerificationPipeline::collect_from_macros().verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{context}: Expected Counterexample, got {result:?}",
    );
}

fn verify_expect_unknown_contains(context: &str, expected_fragment: &str) {
    let result = VerificationPipeline::collect_from_macros().verify();
    match &result {
        VerifyResult::Unknown { reason, .. } => assert!(
            reason.contains(expected_fragment),
            "{context}: Unknown reason should contain '{expected_fragment}', got: {reason}",
        ),
        other => panic!("{context}: Expected Unknown, got {other:?}"),
    }
}

// ============================================================================
// assert_by_nonlinear! tests
// ============================================================================

#[test]
fn test_assert_by_nonlinear_true() {
    common::with_clean_verification(|| {
        assert_by_nonlinear! { true };
        verify_expect_verified("nonlinear true");
    })
}

#[test]
fn test_assert_by_nonlinear_bounded_multiplication() {
    common::with_clean_verification(|| {
        assert_by_nonlinear! { 8u32 * 8u32 <= 64u32 };
        verify_expect_verified("nonlinear 8*8<=64");
    })
}

#[test]
fn test_assert_by_nonlinear_square_nonnegative() {
    common::with_clean_verification(|| {
        assert_by_nonlinear! { 3i32 * 3i32 >= 0i32 };
        verify_expect_verified("nonlinear square nonneg");
    })
}

#[test]
fn test_assert_by_nonlinear_division() {
    common::with_clean_verification(|| {
        assert_by_nonlinear! { 100u32 / 10u32 == 10u32 };
        verify_expect_verified("nonlinear division");
    })
}

#[test]
fn test_assert_by_nonlinear_false_rejected() {
    common::with_clean_verification(|| {
        assert_by_nonlinear! { false };
        verify_expect_counterexample("nonlinear false");
    })
}

#[test]
fn test_assert_by_nonlinear_invalid_bound_rejected() {
    common::with_clean_verification(|| {
        assert_by_nonlinear! { 10u32 * 10u32 <= 50u32 };
        verify_expect_counterexample("nonlinear 10*10<=50");
    })
}

// ============================================================================
// assert_by_bit_vector! tests
// ============================================================================

#[test]
fn test_assert_by_bit_vector_true() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { true };
        verify_expect_verified("bitvector true");
    })
}

#[test]
fn test_assert_by_bit_vector_shift_right() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { (16u64 >> 1) == 8u64 };
        verify_expect_verified("bitvector shift right");
    })
}

#[test]
fn test_assert_by_bit_vector_shift_left() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { (1u64 << 3) == 8u64 };
        verify_expect_verified("bitvector shift left");
    })
}

#[test]
fn test_assert_by_bit_vector_and() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { (0b1100u64 & 0b1010u64) == 0b1000u64 };
        verify_expect_verified("bitvector AND");
    })
}

#[test]
fn test_assert_by_bit_vector_or() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { (0b1100u64 | 0b0011u64) == 0b1111u64 };
        verify_expect_verified("bitvector OR");
    })
}

#[test]
fn test_assert_by_bit_vector_xor() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { (0b1100u64 ^ 0b1010u64) == 0b0110u64 };
        verify_expect_verified("bitvector XOR");
    })
}

#[test]
fn test_assert_by_bit_vector_decrease() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { (10u64 >> 1) < 10u64 };
        verify_expect_verified("bitvector decrease");
    })
}

#[test]
fn test_assert_by_bit_vector_false_rejected() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { false };
        verify_expect_counterexample("bitvector false");
    })
}

#[test]
fn test_assert_by_bit_vector_wrong_shift_rejected() {
    common::with_clean_verification(|| {
        assert_by_bit_vector! { (16u64 >> 1) == 7u64 };
        verify_expect_counterexample("bitvector wrong shift");
    })
}

#[test]
fn test_assert_by_bit_vector_scoped_requires_verified() {
    common::with_clean_verification(|| {
        let x: u32 = 0;
        trust_vc::assume!(x == 0x100u32);
        assert_by_bit_vector! { (x << 1u32) == 0x200u32; requires x == 0x100u32 };
        verify_expect_verified("bitvector scoped requires verified");
    })
}

#[test]
fn test_assert_by_bit_vector_scoped_requires_uses_bitvector_mode() {
    common::with_clean_verification(|| {
        let x: u32 = 0;
        trust_vc::assume!((x | 0x10u32) == 0x30u32);
        assert_by_bit_vector! {
            ((x | 0x10u32) >> 4u32) == 0x3u32;
            requires (x | 0x10u32) == 0x30u32
        };
        verify_expect_verified("bitvector scoped requires with bitwise expression");
    })
}

#[test]
fn test_assert_by_bit_vector_scoped_requires_rejected() {
    common::with_clean_verification(|| {
        let x: u32 = 0;
        assert_by_bit_vector! { (x << 1u32) == 0x200u32; requires x == 0x100u32 };
        verify_expect_counterexample("bitvector scoped requires rejected");
    })
}

// ============================================================================
// assert_by_compute! tests
// ============================================================================

#[test]
fn test_assert_by_compute_true() {
    common::with_clean_verification(|| {
        assert_by_compute! { true };
        verify_expect_verified("compute true");
    })
}

#[test]
fn test_assert_by_compute_arithmetic() {
    common::with_clean_verification(|| {
        assert_by_compute! { 2 + 2 == 4 };
        verify_expect_verified("compute 2+2==4");
    })
}

#[test]
fn test_assert_by_compute_compute_only_arithmetic() {
    common::with_clean_verification(|| {
        assert_by_compute! { 2 + 3 == 5; compute_only };
        verify_expect_verified("compute_only 2+3==5");
    })
}

#[test]
#[allow(clippy::nonminimal_bool)]
fn test_assert_by_compute_comparison_chain() {
    common::with_clean_verification(|| {
        assert_by_compute! { 1 < 2 && 2 < 3 && 3 < 4 };
        verify_expect_verified("compute comparison chain");
    })
}

#[test]
fn test_assert_by_compute_multiplication() {
    common::with_clean_verification(|| {
        assert_by_compute! { 8u64 * 8u64 == 64u64 };
        verify_expect_verified("compute multiplication");
    })
}

#[test]
fn test_assert_by_compute_false_rejected() {
    common::with_clean_verification(|| {
        assert_by_compute! { false };
        verify_expect_counterexample("compute false");
    })
}

#[test]
fn test_assert_by_compute_wrong_arithmetic_rejected() {
    common::with_clean_verification(|| {
        assert_by_compute! { 2 + 2 == 5 };
        verify_expect_counterexample("compute 2+2==5");
    })
}

// ============================================================================
// Combined tests
// ============================================================================

#[test]
fn test_all_solver_hooks_in_sequence() {
    common::with_clean_verification(|| {
        assert_by_nonlinear! { 8u64 * 8u64 <= 100u64 };
        assert_by_bit_vector! { (8u64 >> 1) == 4u64 };
        assert_by_compute! { 8 * 8 == 64 };
        // All three modes now produce real results — all true claims verify
        verify_expect_verified("all solver hooks in sequence");
    })
}

#[test]
fn test_solver_hooks_marker_generated() {
    common::with_clean_verification(|| {
        assert_by_nonlinear! { true };
        assert_by_bit_vector! { true };
        assert_by_compute! { true };
        verify_expect_verified("solver hooks markers");
    })
}

// ============================================================================
// Variable registration tests (#1596)
//
// These tests verify that assert_by_* macros register variables from the
// condition expression via collect_variable_runtime. Runtime `let` bindings
// are not visible to the SMT solver — the variable is unconstrained, so:
// - Nonlinear with variable: solver finds counterexample (e.g. x = 10)
// - Bit vector with variable: solver finds counterexample (unconstrained n=0)
// - Compute with variable: rejected as non-concrete
// ============================================================================

#[test]
fn test_assert_by_nonlinear_with_variable() {
    common::with_clean_verification(|| {
        let x: u32 = 8;
        assert_by_nonlinear! { x * x <= 64u32 };
        // Variable x is unconstrained in SMT — the solver refutes the goal
        // with a genuine model (any |x| > 8, e.g. x = 10 gives 100 > 64).
        // Historically this returned incompleteness-Unknown; the ay NIA
        // ordered-box/zero-bound cut work (2026-07-01) made the unconstrained
        // query decidable, which is strictly more informative and equally
        // sound (the model is a true refutation of the unconstrained goal).
        verify_expect_counterexample("nonlinear with variable");
    })
}

#[test]
fn test_assert_by_bit_vector_with_variable() {
    common::with_clean_verification(|| {
        let n: u64 = 16;
        assert_by_bit_vector! { (n >> 1) == 8u64 };
        // Variable n is unconstrained — solver picks n=0, finds counterexample
        verify_expect_counterexample("bitvector with variable");
    })
}

#[test]
fn test_assert_by_compute_with_variable() {
    common::with_clean_verification(|| {
        let a: u64 = 2;
        let b: u64 = 3;
        assert_by_compute! { a + b == 5u64 };
        verify_expect_unknown_contains(
            "compute with bare runtime variables",
            "by(compute) requires all values to be concrete",
        );
    })
}

#[test]
fn test_assert_by_compute_with_proof_local_bindings_verifies() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn compute_with_local_bindings() {
            let a: u64 = 2;
            let b: u64 = 3;
            assert_by_compute! { a + b == 5u64 };
        }

        compute_with_local_bindings();
    })
}

#[test]
fn test_assert_by_compute_with_assumption_chain_verifies() {
    common::with_clean_verification(|| {
        #[trust_vc::proof]
        fn compute_with_assumption_chain(x: u64) {
            let y: u64 = 3;
            trust_vc::assume!(x == y + 2);
            assert_by_compute! { x == 5u64 };
        }

        compute_with_assumption_chain(0);
    })
}
