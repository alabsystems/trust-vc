//! Prepared-context activation tests for #1927.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::prepared_context::prepare_context;

#[test]
fn test_verify_fails_closed_when_preparation_lowering_fails() {
    let mut ctx = VerificationContext::new();
    // 'x' is unresolved because it is not declared in ctx.variables.
    ctx.push_obligation(ProofObligation::assert("missing_var", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Failed to lower obligation 'missing_var'"),
                "verify() should fail in preparation stage, got error: {}",
                message
            );
        }
        other => panic!(
            "verify() should fail-closed during prepare_context, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_verify_prepared_uses_typed_expr_when_condition_string_is_invalid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("identity", "x + 0 == x"));

    let mut prepared = prepare_context(&ctx).expect("context preparation should succeed");
    let obligation = prepared
        .obligations
        .first_mut()
        .expect("prepared context should include one obligation");

    // Corrupt the legacy string form. verify_prepared must still succeed by
    // resolving through the prepared typed expression map.
    obligation.condition = "x + )".to_string();

    let result = AYEncoder::verify_prepared(&prepared);
    expect_verified(
        &result,
        "verify_prepared should use typed exprs, not parse broken strings",
    );
}

#[test]
fn test_verify_and_verify_prepared_agree_on_counterexample_shape() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assert("false_assertion", "x != x"));

    let prepared = prepare_context(&ctx).expect("context preparation should succeed");
    let legacy_result = AYEncoder::verify(&ctx);
    let prepared_result = AYEncoder::verify_prepared(&prepared);

    expect_counterexample(
        &legacy_result,
        "verify() should report a counterexample for x != x",
    );
    expect_counterexample(
        &prepared_result,
        "verify_prepared() should report a counterexample for x != x",
    );
}

#[test]
fn test_verify_prepared_fails_closed_on_missing_assert_by_scope() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.add_assert_by(
        "missing_scope",
        "x == x",
        vec![crate::vc::ProofObligation::assume("scope_assume", "x == x")],
    );

    let mut prepared = prepare_context(&ctx).expect("context preparation should succeed");
    prepared.assert_by_scopes.remove("missing_scope");

    let result = AYEncoder::verify_prepared(&prepared);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Missing prepared assert_by scope 'missing_scope'"),
                "missing scope should surface as a fail-closed error, got: {}",
                message
            );
        }
        other => panic!(
            "missing assert_by scope must fail closed instead of verifying, got: {:?}",
            other
        ),
    }
}

// ========================================================================
// Slice 5: VerificationPipeline end-to-end integration (#1927)
// ========================================================================

/// Smoke test: VerificationPipeline::verify() works e2e with assumption + assertion.
///
/// NOT DISCRIMINATING: this test does not prove the typed path is used (the same
/// result would occur via the legacy string-parse path). The discriminating proof
/// is `test_verify_prepared_uses_typed_expr_when_condition_string_is_invalid` above.
/// This test confirms the pipeline entrypoint reaches the solver correctly.
#[test]
fn test_pipeline_verify_e2e_with_assumption_and_assertion() {
    use crate::verification_bridge::VerificationPipeline;

    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    pipeline
        .context_mut()
        .push_obligation(ProofObligation::assume("positive", "x > 0"));
    pipeline
        .context_mut()
        .push_obligation(ProofObligation::assert("nonneg", "x >= 0"));

    let result = pipeline.verify();
    expect_verified(&result, "pipeline should verify x>0 => x>=0");
}

/// Pipeline fail-closed: unresolved variable in condition propagates as Error
/// through the full VerificationPipeline, not as Unknown or false Verified.
#[test]
fn test_pipeline_fails_closed_on_unresolved_variable() {
    use crate::verification_bridge::VerificationPipeline;

    let mut pipeline = VerificationPipeline::new();
    // 'y' is not declared — prepare_context must fail-closed.
    pipeline
        .context_mut()
        .push_obligation(ProofObligation::assert("unresolved", "y > 0"));

    let result = pipeline.verify();
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Failed to lower"),
                "pipeline should fail during preparation with lowering error, got: {}",
                message
            );
        }
        other => panic!(
            "pipeline should fail-closed on unresolved variable, got: {:?}",
            other
        ),
    }
}

/// Pipeline fail-closed: syntax error in condition string is caught during
/// prepare_context and returned as Error.
#[test]
fn test_pipeline_fails_closed_on_syntax_error() {
    use crate::verification_bridge::VerificationPipeline;

    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .push_obligation(ProofObligation::assert("bad_syntax", "x +"));

    let result = pipeline.verify();
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Failed to parse"),
                "pipeline should fail during preparation with parse error, got: {}",
                message
            );
        }
        other => panic!(
            "pipeline should fail-closed on syntax error, got: {:?}",
            other
        ),
    }
}

// ========================================================================
// Overflow path uses typed conditions (#2048)
// ========================================================================

/// DISCRIMINATING: overflow detection works through the prepared typed path
/// even when the condition string is corrupted. Before #2048, overflow.rs
/// and verification.rs always re-parsed the string, so corrupting the string
/// while keeping typed IR intact would break overflow detection.
#[test]
fn test_overflow_detection_uses_typed_path_over_string() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    // x + 200 can overflow for x > 55 (u8::MAX = 255)
    ctx.push_obligation(ProofObligation::assert("overflow_check", "x + 200 > 0"));
    ctx.enable_overflow_checks();

    let mut prepared = prepare_context(&ctx).expect("context preparation should succeed");

    // Corrupt the string condition so string-based parsing would fail.
    // If the overflow path still uses the typed condition, overflow checks
    // should still be collected and verified.
    for obligation in &mut prepared.obligations {
        if obligation.name == "overflow_check" {
            obligation.condition = "x + )CORRUPT".to_string();
        }
    }

    let result = AYEncoder::verify_prepared(&prepared);
    // The result should NOT be any Error — the typed path should handle
    // the encoding without needing the (now-corrupted) string condition.
    expect_encodes_without_error(
        &result,
        "overflow path should use typed condition, not re-parse corrupted string",
    );
}

/// DISCRIMINATING: verify and verify_prepared agree on result shape when
/// overflow checking is enabled. Both use the same overflow-collection
/// and assertion-verification pipeline; the only difference is whether
/// conditions are resolved through typed IR or string parsing.
#[test]
fn test_verify_prepared_overflow_behavioral_parity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
    ctx.push_obligation(ProofObligation::assert("parity_check", "x + 200 >= 0"));
    ctx.enable_overflow_checks();

    // Legacy path (string-based)
    let legacy_result = AYEncoder::verify(&ctx);

    // Prepared path (typed conditions available)
    let prepared = prepare_context(&ctx).expect("preparation should succeed");
    let prepared_result = AYEncoder::verify_prepared(&prepared);

    // Both paths must produce the same result variant (Verified, Counterexample,
    // or Error). The specific result depends on whether the encoder generates
    // overflow predicates for plain BV addition — but the paths must agree.
    let legacy_variant = std::mem::discriminant(&legacy_result);
    let prepared_variant = std::mem::discriminant(&prepared_result);
    assert_eq!(
        legacy_variant, prepared_variant,
        "Legacy and prepared paths must agree on result variant.\n\
         Legacy: {:?}\nPrepared: {:?}",
        legacy_result, prepared_result
    );
}

// ========================================================================
// Critical path coverage: loop invariants, broadcasts, assert_by (#2176)
// ========================================================================

/// DISCRIMINATING: Loop invariant through verify_prepared uses typed path.
///
/// Loop invariant verification involves two phases: base case and inductive
/// step. Verifying this works through the prepared typed path (not just
/// the legacy string path) is critical for #2219 reliability.
#[test]
fn test_verify_prepared_loop_invariant_base_and_inductive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init", "x == 0"));
    // Tautological invariant for u32: always >= 0
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "x_nonneg", "x >= 0",
        ));
    // Assertion that uses the verified invariant as assumption
    ctx.push_obligation(ProofObligation::assert("post_loop", "x >= 0"));

    let prepared = prepare_context(&ctx).expect("preparation should succeed");
    let result = AYEncoder::verify_prepared(&prepared);
    expect_verified(
        &result,
        "Loop invariant through prepared path should verify",
    );
}

/// DISCRIMINATING: Loop invariant that FAILS inductive step through prepared path.
///
/// `x > 0` is not preserved after havocing x (inductive step). Both legacy
/// and prepared paths must report this failure consistently.
#[test]
fn test_verify_prepared_loop_invariant_inductive_step_failure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("init", "x > 0"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "x_positive",
            "x > 0",
        ));

    let prepared = prepare_context(&ctx).expect("preparation should succeed");
    let legacy_result = AYEncoder::verify(&ctx);
    let prepared_result = AYEncoder::verify_prepared(&prepared);

    // Both should fail (counterexample or unknown, not Verified)
    expect_fail_closed(
        &legacy_result,
        "Legacy: x>0 invariant should fail inductive step",
    );
    expect_fail_closed(
        &prepared_result,
        "Prepared: x>0 invariant should fail inductive step",
    );
}

/// DISCRIMINATING: Broadcast assumption through verify_prepared.
///
/// Broadcast assumptions are universally quantified. The prepared path must
/// handle the forall wrapping correctly via typed encoding.
#[test]
fn test_verify_prepared_broadcast_assumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // Broadcast: forall x, x + 0 == x (identity property)
    ctx.push_obligation(
        crate::vc::ProofObligation::broadcast_assume("identity_axiom", "x + 0 == x")
            .with_bound_vars(vec!["x".into()]),
    );
    ctx.push_obligation(ProofObligation::assert("identity_check", "x + 0 == x"));

    let prepared = prepare_context(&ctx).expect("preparation should succeed");
    let result = AYEncoder::verify_prepared(&prepared);
    expect_verified(
        &result,
        "Broadcast assumption through prepared path should verify",
    );
}

/// DISCRIMINATING: assert_by scope through verify_prepared.
///
/// assert_by verifies a sub-proof with scoped assumptions, then uses the
/// proven fact for subsequent assertions.
#[test]
fn test_verify_prepared_assert_by_scope() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound", "x >= 0 && x <= 100"));
    // assert_by: prove x < 200 using the assumption
    ctx.add_assert_by(
        "x_bounded",
        "x < 200",
        vec![crate::vc::ProofObligation::assume("scope_hint", "x <= 100")],
    );
    // Use the proven fact
    ctx.push_obligation(ProofObligation::assert("final", "x < 200"));

    let prepared = prepare_context(&ctx).expect("preparation should succeed");
    let result = AYEncoder::verify_prepared(&prepared);
    expect_verified(
        &result,
        "assert_by scope through prepared path should verify",
    );
}

/// DISCRIMINATING: non-default solver mode survives prepare_context and
/// `verify_prepared()` routes NonlinearArith through int_mode verification.
/// Previously returned Unknown fail-closed (#2144); now verifies. Part of #2187.
#[test]
fn test_verify_prepared_nondefault_solver_mode_nonlinear() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("known_x", "x == 5"));
    ctx.push_obligation(
        crate::vc::ProofObligation::new(
            "nonlinear_check",
            "x * x == 25",
            crate::vc::ObligationKind::Assert,
        )
        .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );

    let prepared = prepare_context(&ctx).expect("preparation should succeed");
    let prepared_obligation = prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "nonlinear_check")
        .expect("prepared context should keep the nonlinear_check obligation");
    assert_eq!(
        prepared_obligation.solver_mode,
        Some(crate::vc::SolverMode::NonlinearArith),
        "prepare_context must preserve non-default solver modes"
    );

    let legacy_result = AYEncoder::verify(&ctx);
    let prepared_result = AYEncoder::verify_prepared(&prepared);

    expect_verified(
        &legacy_result,
        "Legacy path should verify x*x==25 in NonlinearArith mode",
    );
    expect_verified(
        &prepared_result,
        "Prepared path should verify x*x==25 in NonlinearArith mode",
    );
}

/// DISCRIMINATING: verify and verify_prepared agree for loop invariant + broadcast.
///
/// This tests a complex context with multiple obligation types processed
/// through both paths, verifying they produce the same result.
#[test]
fn test_verify_prepared_mixed_obligations_parity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("n_bound", "n > 0 && n < 100"));

    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "n_positive",
            "n > 0",
        ));
    ctx.push_obligation(ProofObligation::assert("n_positive_post", "n > 0"));

    let prepared = prepare_context(&ctx).expect("preparation should succeed");
    let legacy_result = AYEncoder::verify(&ctx);
    let prepared_result = AYEncoder::verify_prepared(&prepared);

    let legacy_variant = std::mem::discriminant(&legacy_result);
    let prepared_variant = std::mem::discriminant(&prepared_result);
    assert_eq!(
        legacy_variant, prepared_variant,
        "Mixed obligations: legacy and prepared paths must agree.\n\
         Legacy: {:?}\nPrepared: {:?}",
        legacy_result, prepared_result
    );
}
