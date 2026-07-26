// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral tests for invariant_except_break and loop_ensures (#2417).

use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::{ObligationKind, ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_invariant_except_break_base_case_tautological() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.push_obligation(ProofObligation::invariant_except_break("ieb_true", "true"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "invariant_except_break(true) should verify, got: {:?}",
            result
        );
    });
}

#[test]
fn test_invariant_except_break_rejects_false_condition() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.push_obligation(ProofObligation::invariant_except_break(
            "ieb_false",
            "false",
        ));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "invariant_except_break(false) should fail, got: {:?}",
            result
        );
    });
}

#[test]
fn test_regular_invariant_available_post_loop() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("x_init", "x >= 0"));
        ctx.push_obligation(ProofObligation::loop_invariant("inv_nonneg", "x >= 0"));
        ctx.set_loop_modified_vars("inv_nonneg", vec![]);
        ctx.push_obligation(ProofObligation::assert("post_nonneg", "x >= 0"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "regular loop invariants should remain available post-loop, got: {:?}",
            result
        );
    });
}

/// InvariantExceptBreak base case correctly rejects unsupported conditions.
///
/// With only `x >= 0` assumed, the IEB condition `x < 100` cannot be proven
/// in the base case (counterexample: x=128). This ensures that IEB obligations
/// with insufficient base-case support are properly rejected.
///
/// ARCHITECTURAL NOTE (updated for #2448): Post-loop variable havocking is now
/// implemented. Modified-variable assumptions are rewritten to pre-state form
/// with frame conditions for unmodified variables. The separate behavioral
/// regressions `test_post_loop_assertion_forgets_modified_var_assumptions` and
/// `test_loop_ensures_forgets_modified_var_assumptions` cover the havocking path
/// directly. Pure integration-level InvariantExceptBreak filtering on modified
/// variables is still limited by the current inductive-step approximation.
#[test]
fn test_invariant_except_break_not_available_post_loop() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        // Only assume x >= 0. This does NOT imply x < 100.
        ctx.push_obligation(ProofObligation::assume("x_init", "x >= 0"));
        // Regular invariant: x >= 0 (base case passes from assumption)
        ctx.push_obligation(ProofObligation::loop_invariant("inv_nonneg", "x >= 0"));
        ctx.set_loop_modified_vars("inv_nonneg", vec![]);
        // InvariantExceptBreak: x < 100 (base case FAILS — x >= 0 ↛ x < 100)
        ctx.push_obligation(ProofObligation::invariant_except_break(
            "ieb_bounded",
            "x < 100",
        ));
        ctx.set_loop_modified_vars("ieb_bounded", vec![]);
        ctx.push_obligation(ProofObligation::assert("post_needs_ieb", "x < 100"));

        let result = ctx.verify();
        // Result is Counterexample for ieb_bounded (base case fails), not for
        // the post-loop assertion. This is correct behavior — unprovable
        // invariants should fail at the base case.
        assert!(
            !matches!(result, VerifyResult::Verified),
            "IEB with insufficient base-case support should not verify: {:?}",
            result
        );
    });
}

#[test]
fn test_loop_ensures_verified_when_implied_by_invariants() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("x_init", "x >= 0"));
        ctx.push_obligation(ProofObligation::loop_invariant("inv_nonneg", "x >= 0"));
        ctx.set_loop_modified_vars("inv_nonneg", vec![]);
        ctx.push_obligation(ProofObligation::loop_ensures("le_nonneg", "x >= 0"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "loop_ensures implied by invariants should verify, got: {:?}",
            result
        );
    });
}

#[test]
fn test_loop_ensures_rejected_when_not_implied() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("x_init", "x >= 0"));
        ctx.push_obligation(ProofObligation::loop_invariant("inv_nonneg", "x >= 0"));
        ctx.set_loop_modified_vars("inv_nonneg", vec![]);
        ctx.push_obligation(ProofObligation::loop_ensures("le_eq42", "x == 42"));

        let result = ctx.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "loop_ensures should fail when invariants do not imply it, got: {:?}",
            result
        );
    });
}

#[test]
fn test_loop_ensures_standalone_from_assumptions() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
        ctx.push_obligation(ProofObligation::loop_ensures("le_direct", "x == 42"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "loop_ensures should also work without explicit invariants, got: {:?}",
            result
        );
    });
}

#[test]
fn test_loop_ensures_uses_negated_loop_guard_for_normal_exit() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("x_upper", "x <= 10"));
        ctx.push_obligation(ProofObligation::loop_guard("loop_guard", "x < 10"));
        ctx.push_obligation(ProofObligation::loop_ensures("le_eq10", "x == 10"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "loop_ensures should reason with !guard on the normal-exit path, got: {:?}",
            result
        );
    });
}

#[test]
fn test_post_loop_assume_bool_guard_negation_available_to_assertion() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("b", TrustVcType::Bool);
        ctx.push_obligation(ProofObligation::post_loop_assume(
            "while_b_normal_exit",
            "!(b)",
        ));
        ctx.push_obligation(ProofObligation::assert("post_not_b", "!b"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "normal exit from `while b` should make `!b` available post-loop, got: {:?}",
            result
        );
    });
}

#[test]
fn test_loop_ensures_available_to_post_loop_assertion() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", TrustVcType::Uint { width: 64 });
        ctx.declare_var_typed("limit", TrustVcType::Uint { width: 64 });
        ctx.push_obligation(ProofObligation::assume("i_init", "i == 0"));
        ctx.push_obligation(ProofObligation::assume("limit_init", "limit == 10"));

        ctx.push_obligation(ProofObligation::loop_invariant(
            "limit_stable",
            "limit == 10",
        ));
        ctx.set_loop_modified_vars("limit_stable", vec!["i".to_string()]);
        ctx.push_obligation(ProofObligation::loop_guard("guard", "i < limit"));
        ctx.push_obligation(ProofObligation::loop_ensures("le_i_exited", "i >= 10"));
        ctx.push_obligation(ProofObligation::assert("post_uses_le", "i >= 10"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "verified loop_ensures should be usable by following post-loop assertions, got: {:?}",
            result
        );
    });
}

#[test]
fn test_combined_invariant_except_break_and_loop_ensures() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
        ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("x_init", "x >= 0"));
        ctx.push_obligation(ProofObligation::assume("y_init", "y >= 0"));
        ctx.push_obligation(ProofObligation::loop_invariant("inv_x", "x >= 0"));
        ctx.set_loop_modified_vars("inv_x", vec![]);
        ctx.push_obligation(ProofObligation::invariant_except_break("ieb_y", "y >= 0"));
        ctx.set_loop_modified_vars("ieb_y", vec![]);
        ctx.push_obligation(ProofObligation::loop_ensures("le_both", "x >= 0 && y >= 0"));
        ctx.push_obligation(ProofObligation::assert("post_x", "x >= 0"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "combined loop extension obligations should verify, got: {:?}",
            result
        );
    });
}

#[test]
fn test_obligation_kind_constructors() {
    let ieb = ProofObligation::invariant_except_break("test", "true");
    assert_eq!(ieb.kind(), ObligationKind::InvariantExceptBreak);

    let le = ProofObligation::loop_ensures("test", "true");
    assert_eq!(le.kind(), ObligationKind::LoopEnsures);
}

#[test]
fn test_has_assertions_includes_new_kinds() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::invariant_except_break("ieb", "true"));
    assert!(
        ctx.has_assertions(),
        "InvariantExceptBreak should count as an assertion"
    );

    let mut ctx2 = VerificationContext::new();
    ctx2.push_obligation(ProofObligation::loop_ensures("le", "true"));
    assert!(
        ctx2.has_assertions(),
        "LoopEnsures should count as an assertion"
    );
}

// ========================================================================
// Post-loop variable havocking — #2448
// ========================================================================

/// Post-loop assertions must forget entry assumptions about modified variables.
///
/// Setup: `i` is modified, `n` is unmodified.
/// Assume `i == 5` and `n > 0` at entry.
/// Invariant: `n > 0` on unmodified var — inductive via frame condition.
/// Post-loop assertion: `i == 5`.
///
/// Before #2448: incorrectly verifies because `i == 5` leaks from entry assumptions.
/// After #2448: `i` is modified, so its entry assumption is rewritten to pre-state
/// and no frame condition connects `i` to `i__trust_vc_pre`. The assertion fails.
#[test]
fn test_post_loop_assertion_forgets_modified_var_assumptions() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", TrustVcType::Int { width: 32 });
        ctx.declare_var_typed("n", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("i_entry", "i == 5"));
        ctx.push_obligation(ProofObligation::assume("n_positive", "n > 0"));

        ctx.push_obligation(ProofObligation::loop_invariant("inv_n_positive", "n > 0"));
        ctx.set_loop_modified_vars("inv_n_positive", vec!["i".to_string()]);

        ctx.push_obligation(ProofObligation::assert("post_i_still_5", "i == 5"));

        let result = ctx.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "post-loop assertion about modified var `i` should NOT verify \
             after havocking (entry assumption forgotten): {:?}",
            result
        );
    });
}

/// loop_ensures must also forget entry assumptions about modified variables.
///
/// Same setup as the regular assertion test, but uses LoopEnsures instead.
/// This prevents the same entry-assumption-leak bug from surviving in the
/// dedicated post-loop ensures path.
#[test]
fn test_loop_ensures_forgets_modified_var_assumptions() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", TrustVcType::Int { width: 32 });
        ctx.declare_var_typed("n", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("i_entry", "i == 5"));
        ctx.push_obligation(ProofObligation::assume("n_positive", "n > 0"));

        ctx.push_obligation(ProofObligation::loop_invariant("inv_n_positive", "n > 0"));
        ctx.set_loop_modified_vars("inv_n_positive", vec!["i".to_string()]);

        ctx.push_obligation(ProofObligation::loop_ensures("le_i_still_5", "i == 5"));

        let result = ctx.verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "loop_ensures about modified var `i` should NOT verify \
             after havocking (entry assumption forgotten): {:?}",
            result
        );
    });
}

/// Unmodified variable facts are preserved through post-loop havocking.
///
/// Positive companion to the havocking tests: when `n` is NOT modified,
/// entry assumptions about `n` should still be available post-loop via
/// the frame condition `n == n__trust_vc_pre`.
#[test]
fn test_post_loop_preserves_unmodified_var_assumptions() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("i", TrustVcType::Int { width: 32 });
        ctx.declare_var_typed("n", TrustVcType::Int { width: 32 });
        ctx.push_obligation(ProofObligation::assume("i_entry", "i == 5"));
        ctx.push_obligation(ProofObligation::assume("n_positive", "n > 0"));

        ctx.push_obligation(ProofObligation::loop_invariant("inv_n_positive", "n > 0"));
        ctx.set_loop_modified_vars("inv_n_positive", vec!["i".to_string()]);

        ctx.push_obligation(ProofObligation::assert("post_n_positive", "n > 0"));

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "post-loop assertion about unmodified var `n` should verify \
             (frame condition preserves entry assumption): {:?}",
            result
        );
    });
}
