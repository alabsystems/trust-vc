//! Core quantifier encoding tests — forall/exists semantics and input validation.
//!
//! Tests: reflexivity, contradiction, witness, multiple vars, implication,
//! and error paths (zero args, non-closure, unsupported type, empty params).
//!
//! Issues: #1470, #1500, #1554
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Quantifier encoding tests (Issues #1470, #1500)
// ========================================================================

#[test]
fn test_forall_reflexivity_verified() {
    // forall x: i32. x == x — tautology
    // Skolemized forall — ay-dpll verifies via ground instantiation
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "reflexivity",
        "forall(|x: i32| x == x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forall(|x: i32| x == x) should verify");
}

#[test]
fn test_forall_contradiction_rejected() {
    // forall x: i32. x != x — contradiction, must NOT be Verified
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "contradiction",
        "forall(|x: i32| x != x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall(|x: i32| x != x) must NOT verify (contradiction)",
    );
}

#[test]
fn test_forall_not_all_positive_rejected() {
    // forall x: i32. x > 0 — false (x = 0 is counterexample), must NOT be Verified
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "all_positive",
        "forall(|x: i32| x > 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall(|x: i32| x > 0) must NOT verify (false for x=0)",
    );
}

#[test]
fn test_exists_witness_verified() {
    // exists x: i32. x == 0 — trivially satisfiable
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "exists_zero",
        "exists(|x: i32| x == 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    // ay-dpll returns Unknown for exists quantifiers (#2229 triage)
    expect_verified_or_unknown(&result, "exists(|x: i32| x == 0) should not fail");
}

#[test]
fn test_exists_contradiction_rejected() {
    // exists x: i32. x != x — impossible, no witness exists
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "no_witness",
        "exists(|x: i32| x != x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "exists(|x: i32| x != x) should fail");
}

#[test]
fn test_forall_multiple_vars() {
    // forall x: i32, y: i32. x + y == y + x — commutativity of BV addition.
    // ay-dpll can still return Unknown on multi-variable universal BV
    // quantifiers, so this must remain fail-closed rather than overclaiming.
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "commutativity",
        "forall(|x: i32, y: i32| x + y == y + x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Commutativity should not fail closed");
}

#[test]
fn test_forall_implication() {
    // forall x: i32. x > 5 → x > 0  (implication encoded as !p || q)
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "implication",
        "forall(|x: i32| !(x > 5) || x > 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forall implication should verify");
}

// ========================================================================
// Quantifier input validation error paths (proof_coverage, #1554)
// ========================================================================

/// DISCRIMINATING: forall with zero arguments must error.
/// Covers quantifiers.rs:25-31 (wrong arg count).
#[test]
fn test_forall_zero_args_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("no_args", "forall()"));

    let result = AYEncoder::verify(&ctx);
    expect_error(&result, "forall() with zero arguments must return Error");
}

/// DISCRIMINATING: exists with a non-closure argument must error.
/// Covers quantifiers.rs:34-41 (non-closure argument).
#[test]
fn test_exists_non_closure_arg_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("not_closure", "exists(42)"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "exists(42) with non-closure argument must return Error",
    );
}

/// DISCRIMINATING: forall with unsupported quantifier variable type must error.
/// Covers quantifiers.rs:65-77 (Opaque rejection in quantifier-bound variables).
#[test]
fn test_forall_unsupported_type_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "bad_type",
        "forall(|x: Widget| x == x)",
    ));

    let result = AYEncoder::verify(&ctx);
    match &result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Unsupported type") && message.contains("Widget"),
                "Error message must mention unsupported type 'Widget', got: {}",
                message
            );
        }
        other => panic!(
            "forall with unsupported type Widget must return Error, got: {:?}",
            other
        ),
    }
}

/// DISCRIMINATING: exists with empty closure params must error.
/// Covers quantifiers.rs:82-87 (empty bound_vars).
#[test]
fn test_exists_empty_closure_params_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("no_params", "exists(|| true)"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "exists(|| true) with no bound variables must return Error",
    );
}

// ========================================================================
// Assumption-context forall tests (#2187)
//
// Trigger-less forall in assumptions must use solver.forall() (not
// Skolemize). Skolemization weakens forall to a single instance, which
// is correct for assertions (negated by refutation) but WRONG for
// assumptions where the universal must hold for all values.
// ========================================================================

/// Pure arithmetic forall in assumptions: Int/BV semantics gap (#2227).
///
/// Pure arithmetic forall (no collection references) enters int_mode →
/// bound vars are Sort::Int. But assertion variables are BV-sorted.
/// ay cannot instantiate Int-sorted forall with BV terms → Unknown.
///
/// **Soundness note:** Verified would be WRONG here. The Int forall says
/// `x >= 0 → x + 1 > 0` which is true in mathematical integers (no
/// overflow). But the BV assertion `y + 1 > 0` uses wrapping arithmetic:
/// for y = i32::MAX, y + 1 wraps to i32::MIN, and i32::MIN > 0 is false.
/// So Int-correct assumptions don't imply BV-correct assertions.
///
/// Bridging approaches (bv2int egraph terms, roundtrip identities, ground
/// instantiation) were tested empirically and rejected (#2227 analysis). Current
/// ay-dpll exposes bv2int and multi-round E-matching, but this test is about the
/// remaining semantic gap: Int ground instances do not prove BV assertions.
///
/// The correct fix is Verus-style uniform Int semantics for spec-level
/// assertions (design Option C), which is a large architectural change.
#[test]
fn test_assume_forall_pure_arithmetic_int_bv_sort_gap() {
    let mut ctx = VerificationContext::new();
    ctx.set_skip_retry_cascade(true);
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume(
        "arith_universal",
        "forall(|x: i32| !(x >= 0) || x + 1 > 0)",
    ));
    ctx.push_obligation(ProofObligation::assume("y_nonneg", "y >= 0"));
    ctx.push_obligation(ProofObligation::assert("y_plus_one", "y + 1 > 0"));

    let result = AYEncoder::verify(&ctx);
    // Correct behavior: NOT Verified. Int assumption forall cannot prove
    // BV assertions due to overflow semantics difference (#2227).
    expect_fail_closed(
        &result,
        "Int assume-forall must NOT verify BV assertion — overflow makes it unsound",
    );
}

/// Soundness: assumed universal should NOT make unrelated claims true.
#[test]
fn test_assume_forall_pure_arithmetic_soundness() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume(
        "arith_universal",
        "forall(|x: i32| !(x >= 0) || x + 1 > 0)",
    ));
    ctx.push_obligation(ProofObligation::assume("y_nonneg", "y >= 0"));
    ctx.push_obligation(ProofObligation::assert("y_big", "y > 100"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "assumed universal about +1 should NOT imply > 100");
}
