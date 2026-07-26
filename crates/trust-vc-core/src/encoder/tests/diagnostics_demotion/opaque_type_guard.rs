// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Seq<Widget> has nested Opaque — the verify_typed guard now catches it
/// early via contains_opaque() (#1926). The earlier coarse fallback bucket is
/// gone; the typed guard is preferred because it prevents the solver from
/// running with wrong sorts entirely.
#[test]
fn test_nested_opaque_type_is_rejected_before_solver_run() {
    let mut ctx = VerificationContext::new();
    // Seq<Widget> -> Seq(Opaque("Widget")) -> contains_opaque() = true.
    // Guard in verify_typed catches this BEFORE encoding (#1926 fix).
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<Widget>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("trivial", "x == 42"));

    let result = AYEncoder::verify(&ctx);
    match &result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("unrecognized"),
                "Expected 'unrecognized' in reason, got: {}",
                reason
            );
            assert!(
                reason.contains("Seq<Widget>"),
                "Expected 'Seq<Widget>' in reason, got: {}",
                reason
            );
        }
        other => panic!("Expected Unknown for nested Opaque type, got: {:?}", other),
    }
}

/// f64 variables now stay on the native FP path instead of being demoted
/// before solver setup.
#[test]
fn test_float_type_is_verified_without_pre_solver_demotion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f", crate::ir::TrustVcType::parse_or_opaque("f64"));
    ctx.push_obligation(ProofObligation::assume("self_eq", "f == f"));
    ctx.push_obligation(ProofObligation::assert("reuse_self_eq", "f == f"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "f64 variables should no longer demote before solver setup",
    );
}

/// f32 variables follow the same native FP path.
///
#[test]
fn test_f32_float_type_is_verified_without_pre_solver_demotion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("f", crate::ir::TrustVcType::parse_or_opaque("f32"));
    ctx.push_obligation(ProofObligation::assume("self_eq", "f == f"));
    ctx.push_obligation(ProofObligation::assert("reuse_self_eq", "f == f"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "f32 variables should no longer demote before solver setup",
    );
}

/// Negative companion: Seq<i32> does not hit the opaque-type guard because i32
/// is fully recognized. The same trivially-true assertion should verify.
///
/// Discriminating pair with test_nested_opaque_type_is_rejected_before_solver_run.
#[test]
fn test_known_element_seq_no_demotion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assert("trivial", "x == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Seq<i32> should not trigger demotion");
}
