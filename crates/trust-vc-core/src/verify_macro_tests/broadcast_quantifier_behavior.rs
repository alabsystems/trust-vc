//! Pure quantifier-scope tests for broadcast assumptions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::AYEncoder;
use crate::ir::TrustVcType;
use crate::vc::VerificationContext;

#[test]
fn test_broadcast_with_extra_vars_verifies_correctly() {
    // Integration test: a broadcast lemma (forall n. n >= 0) should apply
    // correctly even when extra variables (x, y) are in scope.
    // The broadcast should be quantified over n only, not (x, y, n).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 64 });

    // Broadcast assumption: forall n. n >= 0 (true for u64)
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_nonneg", "n >= 0")
            .with_bound_vars(vec!["n".to_string()]),
    );

    // Assert something that relies on the broadcast
    ctx.push_obligation(crate::vc::ProofObligation::assert("check_n", "n >= 0"));

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "Broadcast with bound_vars should verify: {:?}",
        result
    );
}

#[test]
fn test_broadcast_over_quantification_demonstrates_bug() {
    // Demonstrates #1618: over-quantified broadcast (bound_vars: None) creates
    // a weaker forall than correctly-scoped broadcast (bound_vars: Some).
    //
    // With bound_vars: None and variables x, y, n in scope, the encoder creates:
    //   (assert (forall ((x BV32) (y BV32) (n BV64)) (>= n 0)))
    // With bound_vars: Some(["n"]), the encoder creates:
    //   (assert (forall ((n BV64)) (>= n 0)))
    //
    // Both are logically equivalent (vacuous quantification), but SMT solvers
    // use E-matching heuristics that can fail to instantiate with extra bound
    // variables. This test verifies the correctly-scoped version works and that
    // the fix produces the right quantifier binding.
    // Scenario 1: Over-quantified (legacy behavior, bound_vars: None)
    let mut ctx_over = VerificationContext::new();
    ctx_over.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx_over.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx_over.declare_var_typed("n", TrustVcType::Uint { width: 64 });
    ctx_over.obligations.push(
        // BUG: quantifies over x, y, n (no bound_vars = legacy over-quantification)
        crate::vc::ProofObligation::broadcast_assume("broadcast_overquantified", "n >= 0"),
    );
    ctx_over.push_obligation(crate::vc::ProofObligation::assert("check_n", "n >= 0"));

    // Scenario 2: Correctly scoped (fix, bound_vars: Some)
    let mut ctx_correct = VerificationContext::new();
    ctx_correct.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx_correct.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx_correct.declare_var_typed("n", TrustVcType::Uint { width: 64 });
    ctx_correct.obligations.push(
        // FIX: quantifies over n only
        crate::vc::ProofObligation::broadcast_assume("broadcast_correct", "n >= 0")
            .with_bound_vars(vec!["n".to_string()]),
    );
    ctx_correct.push_obligation(crate::vc::ProofObligation::assert("check_n", "n >= 0"));

    // The correctly-scoped version must verify
    let result_correct = AYEncoder::verify(&ctx_correct);
    assert!(
        matches!(result_correct, crate::encoder::VerifyResult::Verified),
        "Correctly-scoped broadcast should verify: {:?}",
        result_correct
    );

    // The over-quantified version may or may not verify depending on solver
    // heuristics. We don't assert failure — the key fix is that the code now
    // produces the correctly-scoped version. This test documents the difference.
    let result_over = AYEncoder::verify(&ctx_over);
    let _ = result_over;
}

#[test]
fn test_broadcast_ground_formula_when_no_bound_vars() {
    // When a broadcast lemma has empty bound_vars (e.g., a broadcast with no
    // parameters), the encoder should assert the body as a ground formula
    // instead of creating an empty forall.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });

    // Broadcast with empty bound_vars: should be asserted as ground formula
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_ground", "true")
            .with_bound_vars(vec![]),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("trivial", "true"));

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Verified),
        "Ground broadcast should verify: {:?}",
        result
    );
}

#[test]
fn test_broadcast_bound_vars_with_unresolvable_names_returns_error() {
    // FIX #1629: Unresolvable bound_vars now return an error instead of
    // silently degrading to a ground formula. A typo in bound_vars should
    // be caught, not mask a potential soundness gap.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 64 });

    // Broadcast with a typo in bound_vars — "m" is not a declared variable.
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_typo", "n >= 0")
            .with_bound_vars(vec!["m".to_string()]),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("check", "n >= 0"));

    let result = ctx.verify();
    assert!(
        matches!(result, crate::encoder::VerifyResult::Error { .. }),
        "Broadcast with unresolvable bound_vars should error, got: {:?}",
        result
    );
}
