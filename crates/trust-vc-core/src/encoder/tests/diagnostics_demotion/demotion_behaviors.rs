// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_auxiliary_overflow_precheck_demotes_verified_result() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.enable_overflow_checks();
    ctx.push_obligation(ProofObligation::assume("small_x", "x == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "checked_add_precheck",
        "x + 1 == 6",
    ));

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_OVERFLOW_PRECHECK_DEMOTION);
        AYEncoder::verify(&ctx)
    };

    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.starts_with("demoted:"),
                "auxiliary overflow precheck should demote Verified, got: {reason}"
            );
            assert!(
                reason.contains("function_context_return_type_omitted(1)"),
                "forced auxiliary diagnostic should appear in reason, got: {reason}"
            );
        }
        other => panic!(
            "auxiliary overflow precheck demotion should return Unknown, got: {:?}",
            other
        ),
    }
}

/// Quantifier with bound-variable Seq index access triggers bounds_check_skipped
/// but result should still be Verified (MEDIUM risk, no demotion).
#[test]
fn test_bounds_check_skip_no_demotion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    // Standard Verus pattern: user-provided guard `!(i < len) || ...`
    ctx.push_obligation(ProofObligation::assume("s_has_elems", "s.len() >= 3"));
    ctx.push_obligation(ProofObligation::assert(
        "all_nonneg",
        "forall(|i: u64| !(i < s.len()) || s.index(i) >= 0)",
    ));

    let result = AYEncoder::verify(&ctx);
    if let VerifyResult::Unknown { reason, .. } = &result {
        assert!(
            !reason.starts_with("demoted:"),
            "bounds_check_skipped should not trigger demotion, got: {:?}",
            result
        );
    }
}

/// Trigger-less forall with collection reference is Skolemized (LOW risk).
/// Result should still be Verified.
#[test]
fn test_skolemization_no_demotion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("s_has_elems", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assume(
        "s_elem_positive",
        "s.index(0) >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert("elem_nonneg", "s.index(0) >= 0"));

    let result = AYEncoder::verify(&ctx);
    if let VerifyResult::Unknown { reason, .. } = &result {
        assert!(
            !reason.starts_with("demoted:"),
            "non-quantifier assertion should not be demoted, got: {:?}",
            result
        );
    }
}
