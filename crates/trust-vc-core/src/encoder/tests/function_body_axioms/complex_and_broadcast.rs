//! Complex body axiom tests: ITE/match lowering (#2217), broadcast count
//! double-increment (#2221), recursive base case with direct axiom (#2155),
//! zero-arity recursive axioms, and recursive missing bound var validation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from function_body_axioms/mod.rs (#2145).

use super::*;

/// Complex body axiom: spec function with if/else body.
/// Verifies that the encoder correctly lowers Expr::If through
/// syn::parse_str → lower_syn_expr → encode_trust_vc_expr(TrustVcExpr::Ite).
/// Part of #2217.
#[test]
fn test_spec_fn_ite_body_axiom_verified() {
    let mut ctx = VerificationContext::new();
    register_spec_function(&mut ctx, "abs_val", &[("x", "i32")], "i32");
    add_body_axiom(
        &mut ctx,
        "abs_val",
        &[("x", "i32")],
        "abs_val(x) == { if x >= 0 { x } else { 0 - x } }",
        "abs_val(x)",
    );

    ctx.push_obligation(ProofObligation::assert("abs_pos", "abs_val(5) >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "abs_val(5) >= 0 should verify with if/else body axiom",
    );
}

/// Complex body axiom: nested if/else (clamp function).
/// Verifies nested ITE lowering through the body axiom pipeline.
/// Part of #2217.
#[test]
fn test_spec_fn_nested_ite_body_axiom_verified() {
    let mut ctx = VerificationContext::new();
    register_spec_function(
        &mut ctx,
        "clamp",
        &[("x", "i32"), ("lo", "i32"), ("hi", "i32")],
        "i32",
    );
    add_body_axiom(
        &mut ctx,
        "clamp",
        &[("x", "i32"), ("lo", "i32"), ("hi", "i32")],
        "clamp(x, lo, hi) == { if x < lo { lo } else { if x > hi { hi } else { x } } }",
        "clamp(x, lo, hi)",
    );

    ctx.push_obligation(ProofObligation::assume("bounds", "lo <= hi"));
    ctx.push_obligation(ProofObligation::assert(
        "clamp_in_range",
        "clamp(5, 0, 10) >= 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "clamp(5, 0, 10) >= 0 should verify with nested if/else body axiom",
    );
}

/// Recursive spec functions with a base case verify correctly via the direct
/// defining axiom. ay-dpll's multi-round E-matching can unfold far enough
/// to prove `fact(2) == 2`.
///
/// Previously this was rejected (#2220). Now handled by recursive body-axiom
/// encoding (#2155, #2187).
#[test]
fn test_recursive_spec_with_base_case_verifies_with_direct_axiom() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "fact".to_string(),
        params: vec![(
            "n".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axiom with base case — the direct recursive axiom unfolds this safely.
    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_fact",
            "fact(n) == { if n == 0 { 1 } else { n * fact(n - 1) } }",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["fact(n)".to_string()]]),
    );
    // fact(2) needs 3 unfoldings: fact(2) -> fact(1) -> fact(0) -> base case
    ctx.push_obligation(ProofObligation::assert("fact_2_is_2", "fact(2) == 2"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Recursive spec with base case should verify via the direct recursive axiom",
    );
}

/// Zero-arity recursive body axioms have no quantified variables, so the
/// encoder must assert the axiom directly instead of building a trigger-only
/// forall that ay rejects.
#[test]
fn test_zero_arity_recursive_body_axiom_verifies() {
    let mut ctx = VerificationContext::new();

    ctx.set_function_context(FunctionContext {
        name: "one".to_string(),
        params: vec![],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_one",
            "one() == { if 0 == 0 { 1 } else { one() } }",
        )
        .with_bound_vars(vec![])
        .with_trigger_patterns(vec![vec!["one()".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assert("one_is_1", "one() == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Zero-arity recursive body axiom should verify via direct assertion",
    );
}

/// Recursive body axioms should fail fast on missing bound variables with the
/// same clear scope error used by generic broadcast encoding.
#[test]
fn test_recursive_body_axiom_missing_bound_vars_returns_scope_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

    ctx.set_function_context(FunctionContext {
        name: "down".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: true,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume(
            "__body_axiom_down",
            "down(x) == { if x == 0 { 0 } else { down(x - 1) } }",
        )
        .with_bound_vars(vec!["missing".to_string()])
        .with_trigger_patterns(vec![vec!["down(x)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => assert!(
            message.contains("bound variables not found in scope"),
            "Missing recursive body-axiom bound vars should fail with a scope error, got: {}",
            message
        ),
        other => panic!(
            "Missing recursive body-axiom bound vars should error cleanly, got: {:?}",
            other
        ),
    }
}

/// Verifies broadcast_count is incremented exactly once per broadcast.
/// Previously, both setup_from_context (mod.rs) and
/// parse_and_add_broadcast_assumption (verification/mod.rs) incremented
/// the counter, halving the effective BROADCAST_INSTANCE_CAP from 30 to ~15.
/// Fixed by removing the inner increment (#2221).
///
/// This test creates 20 broadcast lemmas — all under the 30 cap — and
/// verifies they all get quantified treatment (verification succeeds).
#[test]
fn test_broadcast_count_not_double_incremented() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

    register_spec_function(&mut ctx, "g", &[("x", "i32")], "i32");

    // Create 20 broadcast lemmas for the same function.
    // Each is a distinct axiom: g(x) >= -i for i = 0..19.
    for i in 0..20 {
        let condition = format!("g(x) >= 0 - {}", i);
        ctx.obligations.push(
            ProofObligation::broadcast_assume(format!("broadcast_lemma_{}", i), &condition)
                .with_bound_vars(vec!["x".to_string()])
                .with_trigger_patterns(vec![vec!["g(x)".to_string()]]),
        );
    }

    // Assertion that requires the function to exist (trivially true with axioms).
    ctx.push_obligation(ProofObligation::assert("g_bound", "g(5) >= 0 - 19"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "20 broadcasts (under cap 30) should not cause encoder error",
    );
}

/// Complex body axiom: match expression with nested if/else.
/// Verifies Expr::Match → lower_match → encode_match through the body axiom pipeline.
/// Part of #2217.
#[test]
fn test_spec_fn_match_body_axiom_verified() {
    let mut ctx = VerificationContext::new();
    register_spec_function(&mut ctx, "sign", &[("x", "i32")], "i32");
    add_body_axiom(
        &mut ctx,
        "sign",
        &[("x", "i32")],
        "sign(x) == match x { 0 => 0, _ => { if x > 0 { 1 } else { 0 - 1 } } }",
        "sign(x)",
    );

    ctx.push_obligation(ProofObligation::assert("sign_positive", "sign(5) == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign(5) == 1 should verify with match body axiom");
}

/// Discriminating pair for `test_spec_fn_match_body_axiom_verified`: without
/// the body axiom, `sign` remains uninterpreted and `sign(5) == 1` must not
/// verify. Part of #949.
#[test]
fn test_spec_fn_match_body_axiom_missing_axiom_not_provable() {
    let mut ctx = VerificationContext::new();
    register_spec_function(&mut ctx, "sign", &[("x", "i32")], "i32");

    ctx.push_obligation(ProofObligation::assert("sign_positive", "sign(5) == 1"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "sign(5) == 1 should not verify without the match body axiom",
    );
}
