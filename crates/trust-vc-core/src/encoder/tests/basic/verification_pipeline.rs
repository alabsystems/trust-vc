//! Core verification pipeline tests: identity, false assertion, assumptions,
//! multiple assertions, termination measures, constant folding, model extraction.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Dual-path parity tests (string path vs IR path) and string-path scaffolding
//! were removed in #2099 after the string-path parser was deleted.

use super::*;

// ========================================================================
// Basic verification pipeline tests
// ========================================================================

#[test]
fn test_verify_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("identity", "x + 0 == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x + 0 == x should verify for all i32");
}

#[test]
fn test_verify_false_assertion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("false_assertion", "x != x"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "");
}

#[test]
fn test_verify_with_assumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("nonnegative", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x > 0 implies x >= 0");
}

#[test]
fn test_verify_multiple_assertions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // Bound values to prevent overflow
    ctx.push_obligation(ProofObligation::assume("x_pos", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("y_pos", "y > 0"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x < 1000000"));
    ctx.push_obligation(ProofObligation::assume("y_bounded", "y < 1000000"));
    ctx.push_obligation(ProofObligation::assert("sum_pos", "x + y > 0"));
    ctx.push_obligation(ProofObligation::assert("sum_not_zero", "x + y != 0"));

    let result = AYEncoder::verify(&ctx);
    // NOTE: ay-dpll returns Unknown for multi-variable integer constraints
    // when branch-and-bound exceeds MAX_SPLITS (1000 iterations).
    // See the internal ay-unknown-limitation notes for details. This is expected behavior.

    // With bounded values, overflow is prevented and assertions should verify
    match result {
        VerifyResult::Verified => {
            // Expected: assertions are logically valid with bounded values
        }
        VerifyResult::Unknown { .. } => {
            // Acceptable: ay-dpll limitation with multi-variable constraints
            // The solver returns "Unknown" for complex multi-variable constraints
        }
        VerifyResult::Counterexample { .. } => {
            panic!(
                "Should not find counterexample for valid bounded assertions: {:?}",
                result
            );
        }
        // The documented tolerance above is the MAX_SPLITS *resource* limit,
        // which classifies as SolverUnknown — not a permanent theory gap. A
        // NotProved here would mean these bounded assertions are reported as a
        // verification FAILURE, which is a real signal, not something to absorb.
        VerifyResult::NotProved { reason, .. } => {
            panic!("Bounded assertions should not be an incompleteness failure: {reason}");
        }
        VerifyResult::Error { message } => {
            panic!("Should not error: {}", message);
        }
    }
}

#[test]
fn test_termination_measure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("n_nonneg", "n >= 0"));
    ctx.add_measure_nonneg("n");

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "n >= 0 measure on u64 should verify");
}

#[test]
fn test_unbounded_assertion_produces_counterexample() {
    // Test that assertions without assumptions are properly checked
    // The assertion "x >= 0 && x < 10" is not universally true
    // (x could be negative or >= 10), so we expect a counterexample
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("unbounded", "x >= 0 && x < 10"));

    let result = AYEncoder::verify(&ctx);
    // This assertion is not universally true (x could be negative or >= 10)
    // So we expect a counterexample, not verification
    expect_counterexample(&result, "Unbounded assertion should produce counterexample");
}

// ========================================================================
// Constant-only assertion tests (assert_by! pipeline pattern)
// ========================================================================

#[test]
fn test_literal_only_assertion_verifies() {
    // Reproduces the assert_by! pipeline: no variables, parenthesized literal comparison.
    // Translator wraps "5 < 10" as "(5 < 10)" — encoder must constant-fold to true.
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("lit_lt", "(5 < 10)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(5 < 10) should verify via constant folding");
}

#[test]
fn test_multiple_literal_assertions_verify() {
    // Reproduces test_assert_by_chained: three assertions, all constant-foldable.
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("gt", "(5 > 0)"));
    ctx.push_obligation(ProofObligation::assert("lt", "(5 < 10)"));
    ctx.push_obligation(ProofObligation::assert("eq", "(5 == 5)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "All literal assertions should verify");
}

// ========================================================================
// Model extraction tests (Issue #54)
// ========================================================================

#[test]
fn test_counterexample_model_captured_before_pop() {
    // Regression test for #54: Model must be captured before pop()
    // A violable assertion should return a counterexample with model data,
    // not empty/stale data from after pop()
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // x == 0 && x != 0 is unsatisfiable, so NOT(assertion) is SAT
    // This forces the solver to find a counterexample with x assigned
    ctx.push_obligation(ProofObligation::assert("impossible", "x == 0 && x != 0"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            assert_eq!(obligation_name, "impossible");
            // Model MUST be captured before pop() — #54 regression guard.
            // The typed path always produces Some(...) from try_get_model();
            // None here would indicate a regression in model extraction.
            assert!(
                model.is_some(),
                "Model should be Some — #54 regression: model must be captured before pop()"
            );
            let model_str = model.unwrap();
            assert!(
                !model_str.is_empty(),
                "Model should contain assignment data for variable 'x'"
            );
        }
        _ => {
            panic!(
                "x == 0 && x != 0 should always produce Counterexample, got: {:?}",
                result
            );
        }
    }
}

// ========================================================================
// Loop invariant inductive step — proof_coverage gap (P1-214)
// ========================================================================

/// DISCRIMINATING: Tautological loop invariant passes inductive step.
///
/// `x >= 0` with `x: u32` is a tautology (always true for unsigned).
/// The inductive step (Mode 1: havoc-all) should verify because the
/// invariant holds for any unconstrained u32 value.
///
/// If the inductive step check were removed, this would still pass the
/// base case alone — but the inductive step catch below (non-tautology)
/// would become unsound.
#[test]
fn test_loop_invariant_tautology_passes_inductive_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init", "x == 0"));
    // Push a LoopInvariant obligation directly
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "nonneg", "x >= 0",
        ));
    // Also need an assertion after the loop to make context non-empty (#808)
    ctx.push_obligation(ProofObligation::assert("post", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u32 x >= 0 is a tautology — inductive step should pass",
    );
}

/// DISCRIMINATING: Non-tautological loop invariant fails inductive step.
///
/// `x == 0` is NOT a tautology — it holds initially (assumption x==0)
/// but after havocing, x can be any value. The inductive step (havoc-all)
/// should reject this.
///
/// If inductive step verification were removed, this would pass (base case
/// is trivially true from assumption). This test discriminates the presence
/// of the inductive step check.
#[test]
fn test_loop_invariant_non_tautology_fails_inductive_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("init", "x == 0"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "always_zero",
            "x == 0",
        ));
    ctx.push_obligation(ProofObligation::assert("post", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "x == 0 is not a tautology — inductive step should fail",
    );
    // Verify the counterexample mentions "inductive step"
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert!(
            obligation_name.contains("inductive step"),
            "Counterexample should mention 'inductive step', got: {}",
            obligation_name
        );
    }
}

/// DISCRIMINATING: Frame condition inductive step with modified_vars.
///
/// With modified_vars set, only specified variables are havoced.
/// Invariant `y > 0` where only `x` is modified should pass because
/// `y` retains its pre-state constraint (y == 5 > 0).
///
/// If frame conditions were not implemented, all variables would be
/// havoced and `y > 0` would fail (y unconstrained could be 0 or negative).
#[test]
fn test_loop_invariant_frame_condition_preserves_unmodified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 5"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "y_positive",
            "y > 0",
        ));
    // Only x is modified by the loop — y should retain frame condition
    ctx.set_loop_modified_vars("y_positive", vec!["x".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "y > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "y > 0 with only x modified should pass via frame condition",
    );
}

/// Regression test for #2237: measure-mode arithmetic must NOT apply BV wrapping.
///
/// In measure mode (termination proofs), all variables become Sort::Int
/// (unbounded). The typed path's TrustVcExpr still carries the original BV type
/// (e.g., Int{64}), but `encode_int_arith` must bypass `resolve_expr_wrap`
/// when `use_int_arithmetic` is true.
///
/// Without the fix: `a + b` gets signed 64-bit modular wrapping, causing
/// overflow for large values and failing the assertion.
/// With the fix: `a + b` stays as mathematical integer addition.
#[test]
fn test_measure_arithmetic_no_bv_wrapping_regression_2237() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i64"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i64"));

    ctx.push_obligation(ProofObligation::assume("a_pos", "a > 0"));
    ctx.push_obligation(ProofObligation::assume("b_pos", "b > 0"));

    // In Int mode (correct): a + b > a always holds when b > 0.
    // In BV mode with wrapping (the bug): a + b wraps to [-2^63, 2^63-1],
    // so for large a, b the sum can be negative → a + b < a.
    ctx.add_measure_decreases_obligation("sum_gt", "a + b > a", None);

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Measure arithmetic should use unbounded Int (no BV wrapping). If this fails with Counterexample, the #2237 fix is missing");
}

/// Regression test for #2237: negation in measure mode must not wrap.
///
/// Tests the logic.rs path: negation (`-n`) in measure mode should produce
/// the mathematical negation, not signed-BV negation.
/// For i8 in BV mode, `-(-128) = -128` (overflow). In Int mode, `-(-128) = 128`.
#[test]
fn test_measure_negation_no_bv_wrapping_regression_2237() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i64"));

    ctx.push_obligation(ProofObligation::assume("n_neg", "n < 0"));

    // In Int mode: -n > 0 when n < 0, always true.
    // In BV mode: -n could overflow when n = i64::MIN → -n = i64::MIN (negative).
    ctx.add_measure_decreases_obligation("neg_pos", "-n > 0", None);

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Measure negation should use unbounded Int (no BV wrapping). If this fails, the #2237 logic.rs fix is missing");
}
