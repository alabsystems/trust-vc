//! Mode 1 (havoc-all) and Mode 2 (frame condition) inductive step tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from inductive_step_coverage/mod.rs (#2145).

use super::*;

// ============================================================
// Mode 1: Havoc-all additional coverage
// ============================================================

/// Mode 1: havoc-all correctly rejects non-tautological invariant
/// that depends on initial assumptions, even with function context.
///
/// The existing test_loop_invariant_non_tautology_fails_inductive_step
/// does not use a function context. This test verifies that the
/// function context path in havoc-all also works correctly.
#[test]
fn test_inductive_havoc_all_with_function_context() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    });
    ctx.push_obligation(ProofObligation::assume("init", "n == 0"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "n_eq_zero",
            "n == 0",
        ));
    ctx.push_obligation(ProofObligation::assert("post", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    // n == 0 is not a tautology — havoc-all should reject it
    expect_counterexample(
        &result,
        "n == 0 with function context should fail inductive step",
    );
}

/// Mode 1: tautological invariant on unsigned type passes havoc-all.
///
/// `x <= u16::MAX` (i.e., `x <= 65535`) is always true for u16 due to
/// bit-vector semantics. The havoc-all mode should accept this because
/// any unconstrained u16 value is ≤ 65535.
#[test]
fn test_inductive_havoc_all_unsigned_tautology() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u16"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "u16_bounded",
            "x <= 65535",
        ));
    ctx.push_obligation(ProofObligation::assert("post", "x <= 65535"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "u16 x <= 65535 is a tautology — should pass havoc-all",
    );
}

// ============================================================
// Mode 2: Frame condition coverage
// ============================================================

/// Frame condition with loop guard: invariant depends on guard.
///
/// `sum >= 0 && i <= n` where `i` and `sum` are modified, `n` is
/// unmodified, and the loop guard is `i < n`. The invariant `i <= n`
/// should pass because:
/// - Pre-state: i <= n (assumed as inductive hypothesis)
/// - Loop guard: i < n for pre-state (strengthens to i < n)
/// - Post-state: n == n__trust_vc_pre (frame condition for n)
/// - i is havoced but the invariant only needs i <= n where n is preserved.
///
/// Actually `i <= n` fails because i is havoced without upper bound.
/// But `sum >= 0` alone on i32 is not a tautology.
/// Let's test a simpler scenario: loop guard helps preserve invariant.
#[test]
fn test_frame_condition_with_loop_guard() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("limit", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_limit", "limit == 10"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "limit_stable",
            "limit == 10",
        ));
    ctx.set_loop_modified_vars("limit_stable", vec!["x".to_string()]);
    ctx.add_loop_guard("limit_stable", "x < limit");
    ctx.push_obligation(ProofObligation::assert("post", "limit == 10"));

    let result = AYEncoder::verify(&ctx);
    // limit is unmodified → frame condition asserts limit == limit__pre.
    // Since limit__pre == 10 (from inductive hypothesis), limit == 10 holds.
    expect_verified(
        &result,
        "Unmodified limit should be preserved via frame condition",
    );
}

/// Frame condition with multiple variables: mixed modified/unmodified.
///
/// Three variables: a (modified), b (unmodified), c (unmodified).
/// Invariant: `b == 3` (only references unmodified variable).
/// Since b is unmodified, its frame condition preserves its value.
/// Uses simple equality to avoid BV solver timeout on cross-variable arithmetic.
#[test]
fn test_frame_condition_multiple_unmodified_vars() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("c", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_a", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("init_b", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("init_c", "c == 7"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "b_stable", "b == 3",
        ));
    // Only a is modified by the loop — b and c are preserved
    ctx.set_loop_modified_vars("b_stable", vec!["a".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "b == 3"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "b == 3 with b unmodified should pass frame condition",
    );
}

/// Frame condition correctly rejects invariant on modified variable.
///
/// Variable `x` is modified, invariant is `x > 0`. Even though the
/// initial assumption sets x == 5, the inductive step havocs x
/// (since it's in modified_vars) and the invariant fails because
/// x could be 0 or negative.
#[test]
fn test_frame_condition_rejects_modified_var_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 1"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "x_positive",
            "x > 0",
        ));
    // x IS modified — no frame condition protects it
    ctx.set_loop_modified_vars("x_positive", vec!["x".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "x >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "x > 0 with x modified should fail inductive step");
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert!(
            obligation_name.contains("inductive step"),
            "Should mention 'inductive step', got: {}",
            obligation_name
        );
    }
}

/// Frame condition with empty modified_vars = all vars preserved.
///
/// When modified_vars is set to an empty list, no variables are havoced
/// and ALL variables get frame conditions. Even a non-tautological
/// invariant should pass because every variable equals its pre-state.
#[test]
fn test_frame_condition_empty_modified_vars_all_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 42"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 7"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "both_stable",
            "x == 42 && y == 7",
        ));
    // Empty modified_vars = nothing havoced, all preserved
    ctx.set_loop_modified_vars("both_stable", vec![]);
    ctx.push_obligation(ProofObligation::assert("post", "x == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Empty modified_vars should preserve all values");
}

/// Frame condition with function context in inductive step.
///
/// Ensures the function_context registration path in
/// verify_inductive_step_frame_condition works correctly.
#[test]
fn test_frame_condition_with_function_context() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "helper".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    });
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));
    ctx.push_obligation(ProofObligation::assume("init_n", "n == 100"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "n_constant",
            "n == 100",
        ));
    ctx.set_loop_modified_vars("n_constant", vec!["i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "n == 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "n constant with function context should pass frame condition",
    );
}
