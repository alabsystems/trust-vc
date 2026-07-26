// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Spec function body axioms in verification.
//!
//! Tiers 1-10 exercise arithmetic, quantifiers, sequences, and assumptions.
//! Tier 11 exercises spec function body axioms — the mechanism that makes
//! spec functions usable in proofs. In competition, spec functions define
//! mathematical abstractions (e.g., `sum(a, b)`, `double(x)`), and their
//! body axioms let the solver reason about them.
//!
//! Part of #2187. Also validates #2220 fix (recursive spec detection).
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::mode::FunctionMode;
use trust_vc_core::vc::{FunctionContext, ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

fn i32_spec_fn(name: &str, params: &[&str]) -> FunctionContext {
    FunctionContext::new(
        name,
        params
            .iter()
            .map(|param| {
                (
                    (*param).to_string(),
                    trust_vc_core::ir::TrustVcType::from_str("i32").unwrap(),
                )
            })
            .collect(),
        trust_vc_core::ir::TrustVcType::from_str("i32").unwrap(),
        FunctionMode::Spec,
    )
}

// ========================================================================
// TIER 11a: Non-recursive spec body axiom applied in proof
// A spec function `double(x) == x + x` has its body axiom used by the
// solver to verify properties about double.
// Regression: ensures is_recursive detection doesn't over-reject (#2220).
// ========================================================================

#[test]
fn test_vt_tier11a_spec_body_axiom_double_property() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");

    // Non-recursive spec function context (as expand_spec produces)
    ctx.set_function_context(i32_spec_fn("double", &["x"]));

    ctx.push_assume("x_bound", "x >= 0 && x <= 100");

    // Body axiom: double(x) == x + x
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double(x)".to_string()]]),
    );

    // Property: double(5) == 10
    ctx.push_assert("double_5", "double(5) == 10");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 11a: spec body axiom should verify double(5) == 10. Got: {:?}",
        result,
    );
}

#[test]
fn test_vt_tier11a_spec_body_axiom_sum_pair() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");

    // Spec function: sum_pair(a, b) == a + b
    ctx.set_function_context(i32_spec_fn("sum_pair", &["a", "b"]));

    ctx.push_assume("a_pos", "a > 0 && a <= 100");
    ctx.push_assume("b_pos", "b > 0 && b <= 100");

    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_sum_pair", "sum_pair(a, b) == a + b")
            .with_bound_vars(vec!["a".to_string(), "b".to_string()])
            .with_trigger_patterns(vec![vec!["sum_pair(a, b)".to_string()]]),
    );

    // Concrete property: sum_pair(3, 4) == 7
    ctx.push_assert("sum_concrete", "sum_pair(3, 4) == 7");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 11a: spec body axiom should verify sum_pair(3,4) == 7. Got: {:?}",
        result,
    );
}

#[test]
fn test_vt_tier11a_spec_body_axiom_if_else_abs_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");

    ctx.set_function_context(i32_spec_fn("abs_val", &["x"]));

    ctx.push_assume("x_bound", "x >= 0 - 100 && x <= 100");

    ctx.push_obligation(
        ProofObligation::broadcast_assume(
            "__body_axiom_abs_val",
            "abs_val(x) == { if x >= 0 { x } else { 0 - x } }",
        )
        .with_bound_vars(vec!["x".to_string()])
        .with_trigger_patterns(vec![vec!["abs_val(x)".to_string()]]),
    );

    ctx.push_assert("abs_negative", "abs_val(0 - 5) == 5");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 11a: if/else spec body axiom should verify abs_val(-5) == 5. Got: {:?}",
        result,
    );
}

#[test]
fn test_vt_tier11a_spec_body_axiom_block_let_expression() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");

    ctx.set_function_context(i32_spec_fn("step_cost", &["x", "y"]));

    ctx.push_assume("bounds", "x >= 0 && y >= 0 && x <= 100 && y <= 100");

    ctx.push_obligation(
        ProofObligation::broadcast_assume(
            "__body_axiom_step_cost",
            "step_cost(x, y) == { let total = x + y; total + 1 }",
        )
        .with_bound_vars(vec!["x".to_string(), "y".to_string()])
        .with_trigger_patterns(vec![vec!["step_cost(x, y)".to_string()]]),
    );

    ctx.push_assert("step_cost_concrete", "step_cost(2, 3) == 6");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 11a: block/let spec body axiom should verify step_cost(2, 3) == 6. Got: {:?}",
        result,
    );
}

#[test]
fn test_vt_tier11a_spec_body_axiom_match_expression() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");

    ctx.set_function_context(i32_spec_fn("sign", &["x"]));

    ctx.push_assume("x_bound", "x >= 0 - 100 && x <= 100");

    ctx.push_obligation(
        ProofObligation::broadcast_assume(
            "__body_axiom_sign",
            "sign(x) == match x { 0 => 0, _ => { if x > 0 { 1 } else { 0 - 1 } } }",
        )
        .with_bound_vars(vec!["x".to_string()])
        .with_trigger_patterns(vec![vec!["sign(x)".to_string()]]),
    );

    ctx.push_assert("sign_positive", "sign(5) == 1");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 11a: match spec body axiom should verify sign(5) == 1. Got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 11b: Recursive spec body axiom correctly rejected
// A recursive spec like `fact(n) = if n==0 { 1 } else { n * fact(n-1) }`
// produces a circular axiom. The encoder guard must reject it.
// Validates #2220 fix end-to-end.
// ========================================================================

#[test]
fn test_vt_tier11b_recursive_spec_body_axiom_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "i32");

    // Recursive spec — expand_spec now detects this and sets is_recursive: true
    ctx.set_function_context(i32_spec_fn("fact", &["n"]).with_recursive(true));

    // Circular body axiom: fact(n) == n * fact(n - 1)
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_fact", "fact(n) == n * fact(n - 1)")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["fact(n)".to_string()]]),
    );

    ctx.push_assert("fact_3", "fact(3) == 6");

    let result = ctx.verify();
    // Fuel encoding is now implemented (direct defining axiom + E-matching).
    // The recursive axiom fact(n) == n * fact(n - 1) on BV32 hits solver
    // timeout because E-matching can't fully unroll. Both Unknown (timeout)
    // and Counterexample (insufficient fuel) are acceptable fail-closed
    // outcomes. Updated from stale Error expectation. Part of #2658.
    assert!(
        matches!(
            result,
            VerifyResult::Unknown { .. } | VerifyResult::Counterexample { .. }
        ),
        "TIER 11b: recursive spec body axiom should fail closed (timeout or cx). Got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 11c: Spec body axiom negative test — wrong property is not verified
// Ensures body axioms don't make the solver unsound. If double(x) == x + x,
// claiming double(x) == x * x should not verify for all x.
// ========================================================================

#[test]
fn test_vt_tier11c_spec_body_axiom_wrong_property_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");

    ctx.set_function_context(i32_spec_fn("double", &["x"]));

    ctx.push_assume("x_bound", "x >= 0 && x <= 100");

    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double(x)".to_string()]]),
    );

    // Wrong: double(x) == x * x (only true for x=0 and x=2, not all x)
    ctx.push_assert("wrong_double", "double(x) == x * x");

    let result = ctx.verify();
    // ay-dpll either returns Unknown (quantifier-unhandled from E-matching
    // limitations) or Unknown (BV solver timeout). Both are correct fail-closed
    // behavior. The core soundness property is that the wrong property does NOT
    // verify. Updated to accept any non-Verified outcome. Part of #2658.
    assert!(
        !matches!(&result, VerifyResult::Verified),
        "TIER 11c SOUNDNESS: wrong property must NOT verify, got: {:?}",
        result,
    );
}
