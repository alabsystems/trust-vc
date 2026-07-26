//! Coverage tests for verify_legacy branch paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers P1 gaps identified in proof_coverage audit:
//! - Empty context rejection (#808)
//! - Assumptions-only rejection (#1859)
//! - Opaque variable rejection (#1926)
//! - CallSite mode: Requires as assertion
//! - AssertBy scoped assumption isolation
//!
//! Re: #2134

use super::*;

// ============================================================
// Empty context / assumptions-only paths
// ============================================================

/// Empty context (no obligations at all) returns Error.
///
/// Soundness bug #808: a context with zero obligations should not verify.
#[test]
fn test_verify_legacy_empty_context_returns_error() {
    let ctx = VerificationContext::new();
    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "Empty context should return Error");
    if let VerifyResult::Error { message } = &result {
        assert!(
            message.contains("empty context") || message.contains("no obligations"),
            "Error should mention empty context, got: {}",
            message
        );
    }
}

/// Context with only assumptions and no assertions returns Error (#1859).
///
/// A context with requires() but no ensures() should NOT return Verified.
/// This masks missing postconditions and accepts contradictory assumptions.
#[test]
fn test_verify_legacy_assumptions_only_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("pre", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "Assumptions-only context should return Error");
    if let VerifyResult::Error { message } = &result {
        assert!(
            message.contains("only assumptions") || message.contains("nothing to prove"),
            "Error should mention only-assumptions, got: {}",
            message
        );
    }
}

/// Context with Requires in BodyLevel mode (default) = assumption, no assertion.
///
/// A requires-only context in BodyLevel mode has no assertions, so
/// it should return the "nothing to prove" error.
#[test]
fn test_verify_legacy_requires_bodylevel_as_assumption_only() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations
        .push(crate::vc::ProofObligation::requires("pre", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Requires-only in BodyLevel should return Error (nothing to prove)",
    );
}

// ============================================================
// Opaque variable rejection
// ============================================================

/// Context with Opaque-typed variables returns Unknown (#1926).
///
/// TrustVcType::Opaque maps unrecognized types to Sort::Int, which would
/// allow spurious proofs. The verifier rejects these with Unknown.
#[test]
fn test_verify_legacy_opaque_variable_returns_unknown() {
    let mut ctx = VerificationContext::new();
    // Declare a variable with an unrecognized type
    ctx.push_variable(crate::vc::VariableDecl {
        bounded_len: false,
        name: "s".to_string(),
        ty: crate::ir::TrustVcType::Opaque("MyStruct".to_string()),
    });
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("check", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_unknown(&result, "Opaque variable should return Unknown");
    if let VerifyResult::Unknown { reason, .. } = &result {
        assert!(
            reason.contains("unrecognized types") || reason.contains("MyStruct"),
            "Unknown should mention opaque type, got: {}",
            reason
        );
    }
}

// ============================================================
// CallSite mode: Requires becomes assertion
// ============================================================

/// In CallSite mode, Requires is treated as an assertion (must be proved).
///
/// A requires("x > 0") with assumption x == 5 should be Verified.
#[test]
fn test_verify_legacy_callsite_requires_as_assertion_verified() {
    let mut ctx = VerificationContext::new().with_call_site_mode();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("known", "x == 5"));
    ctx.obligations
        .push(crate::vc::ProofObligation::requires("pre", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CallSite requires with x==5 should verify x>0");
}

/// In CallSite mode, Requires is treated as an assertion — can fail.
///
/// A requires("x > 0") with no supporting assumptions should fail.
#[test]
fn test_verify_legacy_callsite_requires_as_assertion_counterexample() {
    let mut ctx = VerificationContext::new().with_call_site_mode();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations
        .push(crate::vc::ProofObligation::requires("pre", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "CallSite requires without support should produce counterexample",
    );
}

// ============================================================
// AssertBy scoped assumptions
// ============================================================

/// AssertBy with scoped assumption: proven condition becomes assumption.
///
/// assert_by("goal", "x + y == 10") with scoped assumption "y == 5"
/// and global assumption "x == 5" should verify.
/// Then a subsequent assertion "x + y == 10" should also verify
/// because the proven assert_by condition becomes an assumption.
#[test]
fn test_verify_legacy_assert_by_scoped_then_available() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("known_x", "x == 5"));

    // Add assert_by with scoped proof assumptions
    ctx.add_assert_by(
        "sum_proof",
        "x + y == 10",
        vec![crate::vc::ProofObligation::assume("scope_y", "y == 5")],
    );

    // Subsequent assertion: uses the proven assert_by as assumption
    ctx.push_obligation(ProofObligation::assert("check_sum", "x + y == 10"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "assert_by proven condition should be available as assumption",
    );
}

/// AssertBy scoped assumptions do NOT leak to subsequent assertions
/// (only the proven conclusion does).
///
/// Scoped assumption "z == 42" is used to prove "x > 0" (trivially,
/// since x == 5 from global). Then we check that "z == 42" is NOT
/// available outside the scope — z is unconstrained globally.
#[test]
fn test_verify_legacy_assert_by_scope_does_not_leak() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("z", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("known_x", "x == 5"));

    // assert_by with scoped assumption "z == 42" to prove "x > 0"
    // The conclusion x > 0 is trivially true from x == 5.
    // The scoped assumption z == 42 is irrelevant to the proof but
    // should not leak to subsequent assertions.
    ctx.add_assert_by(
        "trivial_proof",
        "x > 0",
        vec![crate::vc::ProofObligation::assume("scope_z", "z == 42")],
    );

    // This assertion tries to use z == 42, which should NOT be available
    // because it was a scoped assumption inside the assert_by.
    // The proven conclusion (x > 0) doesn't constrain z.
    ctx.push_obligation(ProofObligation::assert("check_z", "z == 42"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Scoped assumption z==42 should not leak to outer assertions",
    );
}
