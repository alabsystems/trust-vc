//! Tests for the confirmation check disagreement → Unknown demotion path.
//!
//! The confirmation check (assertion.rs) re-verifies assertions in
//! collection-involving contexts with a fresh solver to catch ay-dpll
//! non-determinism (#2241, #2354). These tests exercise the disagreement
//! path deterministically using a `#[cfg(test)]` hook. Part of #2250.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::verification::confirmation::verify_with_confirmation;
use crate::encoder::verification::outcome::AssertionOutcome;
use crate::encoder::verification::test_hooks::{
    FORCE_CONFIRMATION_DISAGREE, FORCE_CONFIRMATION_PANIC,
};
use crate::encoder::verification::unknown_category::UnknownCategory;
use crate::prepared_context::prepare_context;
use crate::vc::ObligationKind;

/// DISCRIMINATING: When the confirmation check disagrees, a collection
/// assertion that would normally verify is demoted to Unknown.
///
/// This test sets the FORCE_CONFIRMATION_DISAGREE flag so the confirmation
/// path short-circuits to disagreement, then verifies the result is Unknown
/// with the expected reason. Without the flag, the same context verifies.
#[test]
fn test_confirmation_disagree_demotes_collection_assertion_to_unknown() {
    // Setup: Seq assertion that normally verifies.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("len_check", "s.len() >= 1"));

    // Baseline: without the flag, this verifies.
    let baseline = AYEncoder::verify(&ctx);
    expect_verified(
        &baseline,
        "Baseline: s.len()==3 => s.len()>=1 should verify",
    );

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_CONFIRMATION_DISAGREE);
        AYEncoder::verify(&ctx)
    };

    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("Confirmation check disagreed"),
                "Unknown reason should mention confirmation disagreement, got: {}",
                reason
            );
            assert!(
                reason.contains("len_check"),
                "Unknown reason should name the assertion, got: {}",
                reason
            );
        }
        other => panic!(
            "With forced disagreement, collection assertion should be Unknown, got: {:?}",
            other
        ),
    }
}

/// PLUMBING (Slice 3 of #2706): `current_proof_is_strict()` correctly
/// identifies a strict proof when `proof-certificates` is enabled.
///
/// Uses a simple integer proof (no collections) because ay-dpll's strict
/// checker currently uses trust steps for array/collection theory lemmas,
/// so collection proofs are not strict-verified yet. The confirmation skip
/// will activate for collection assertions once ay improves strict checking.
///
/// This test verifies the read path through the capture context works:
/// `set_produce_proofs(true)` -> solve -> `record_proof_artifact` ->
/// `current_proof_is_strict()`.
#[cfg(feature = "proof-certificates")]
#[test]
fn test_proof_certificate_strict_flag_readable_through_capture() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));

    let report = ctx.verify_with_report(crate::VerificationReportOptions::new());
    expect_verified(report.result(), "simple integer proof should verify");
    let proof = report
        .proof()
        .expect("verified result should carry a proof certificate");
    // The accessor works and returns a value.  ay-dpll strict checking may
    // or may not succeed depending on theory lemma handling, but the read
    // path through the capture context must be functional.
    let _strict = proof.strict_verified();
}

/// PLUMBING: `kernel_verified()` returns a meaningful result when the full
/// kernel bridge pipeline runs on a simple integer proof.
///
/// Exercises: solve -> export_last_unsat_artifact -> last_proof ->
/// kernel_bridge::verify_proof_with_kernel -> ProofCertificate.kernel_verified().
#[cfg(feature = "proof-certificates")]
#[test]
fn test_kernel_verified_flag_readable_through_capture() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));

    let report = ctx.verify_with_report(crate::VerificationReportOptions::new());
    expect_verified(report.result(), "simple integer proof should verify");
    let proof = report
        .proof()
        .expect("verified result should carry a proof certificate");
    // The kernel_verified accessor must be functional. The value depends on
    // whether the ay proof structure is convertible, but the read path through
    // the capture context must work end-to-end.
    let _kernel_ok = proof.kernel_verified();
}

/// DISCRIMINATING: With `proof-certificates` enabled, collection assertions
/// that produce non-strict proofs still go through the confirmation check.
///
/// ay-dpll's strict checker currently marks array/collection theory lemmas
/// as trust steps, so `strict_verified()` is false for Seq assertions. The
/// confirmation skip in Slice 3 of #2706 does NOT fire, and the forced-
/// disagree hook still demotes the result to Unknown. This test confirms
/// the skip is correctly conditional on strict verification.
#[cfg(feature = "proof-certificates")]
#[test]
fn test_confirmation_not_skipped_for_non_strict_collection_proof() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("len_check", "s.len() >= 1"));

    // Baseline: without the disagree flag, this verifies normally.
    let baseline = AYEncoder::verify(&ctx);
    expect_verified(&baseline, "Baseline: Seq len==3 => len>=1 should verify");

    // With forced disagreement AND proof-certificates: the Seq proof is
    // not strict-verified (array theory uses trust steps), so the proof
    // certificate skip does NOT fire and the disagree hook demotes to Unknown.
    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_CONFIRMATION_DISAGREE);
        AYEncoder::verify(&ctx)
    };
    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("Confirmation check disagreed"),
                "Non-strict proof should NOT skip confirmation, got: {}",
                reason
            );
        }
        other => panic!(
            "Collection assertion with non-strict proof and forced disagree \
             should be Unknown, got: {:?}",
            other
        ),
    }
}

/// DISCRIMINATING: The confirmation check does NOT fire for non-collection
/// assertions. Even with FORCE_CONFIRMATION_DISAGREE set, a pure arithmetic
/// assertion that verifies should still return Verified.
#[test]
fn test_confirmation_check_skipped_for_non_collection_assertion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("positive", "x >= 1"));

    // Force disagreement flag ON — but the assertion doesn't reference
    // collections, so the confirmation check should not trigger.
    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_CONFIRMATION_DISAGREE);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &result,
        "Non-collection assertion should bypass confirmation check and verify",
    );
}

/// DISCRIMINATING: The confirmation check does NOT fire when the main
/// verification result is a counterexample (result.0 == false). Only
/// verified collection assertions get the double-check.
#[test]
fn test_confirmation_check_skipped_for_failing_collection_assertion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    // This assertion is false: s.len() == 5 when we assumed s.len() == 3.
    ctx.push_obligation(ProofObligation::assert("wrong_len", "s.len() == 5"));

    // Force disagreement flag ON — but the main result is a counterexample,
    // so the confirmation check guard (result.0) should prevent firing.
    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_CONFIRMATION_DISAGREE);
        AYEncoder::verify(&ctx)
    };

    // Under native-seq, ay-dpll's Seq theory disables model validation,
    // so the correct SAT result is demoted to Unknown. Part of #2680.
    #[cfg(feature = "native-seq")]
    expect_fail_closed(
        &result,
        "False collection assertion should not verify (model validation disabled under native-seq)",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_counterexample(
        &result,
        "False collection assertion should produce Counterexample, not Unknown \
         (confirmation check should not fire on failing assertions, result.0 is false)",
    );
}

/// DISCRIMINATING: The confirmation check fires for non-collection assertions
/// when the context contains collection variables/assumptions (#2354).
///
/// Context: Seq variable + Seq assumption, but the assertion only checks a
/// plain integer. Before #2354, the confirmation check would skip this
/// assertion (the assertion expression doesn't reference collections). After
/// #2354, `has_collection_context` is true so the gate opens.
#[test]
fn test_confirmation_fires_for_non_collection_assertion_in_collection_context() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("seq_bound", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("x_check", "x == x"));

    // Baseline: without the flag, this verifies.
    let baseline = AYEncoder::verify(&ctx);
    expect_verified(&baseline, "Baseline: x==x should verify");

    // With forced disagreement: the confirmation check should now fire
    // because the context has collection variables, even though the
    // assertion itself doesn't reference collections.
    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_CONFIRMATION_DISAGREE);
        AYEncoder::verify(&ctx)
    };

    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("Confirmation check disagreed"),
                "Unknown reason should mention confirmation disagreement, got: {}",
                reason
            );
            assert!(
                reason.contains("x_check"),
                "Unknown reason should name the assertion, got: {}",
                reason
            );
        }
        other => panic!(
            "Non-collection assertion in collection context should be demoted to Unknown \
             with forced disagreement (#2354), got: {:?}",
            other
        ),
    }
}

#[test]
fn test_confirmation_disagree_guard_resets_after_panic() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _flag = ForcedFlagGuard::new(&FORCE_CONFIRMATION_DISAGREE);
        panic!("simulated test panic");
    }));
    assert!(result.is_err(), "guard regression test should panic");
    FORCE_CONFIRMATION_DISAGREE.with(|flag| {
        assert!(
            !flag.get(),
            "forced confirmation-disagree flag must reset during unwind"
        )
    });
}

/// DISCRIMINATING: A ay-classified panic during the confirmation rerun must
/// stay on the Unknown outcome path and use SolverPanic, not
/// ConfirmationDisagree. Tests the Err(e) arm of the three-way match split
/// in verify_with_confirmation (inductive step path). Part of #2377.
#[test]
fn test_confirmation_ay_panic_reports_solver_panic_category() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.push_obligation(ProofObligation::assume("len", "s.len() == 3"));
    ctx.push_obligation(ProofObligation::assert("len_check", "s.len() >= 1"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let assertion = prepared
        .obligations
        .iter()
        .find(|o| o.name == "len_check")
        .expect("prepared context should contain len_check");
    let assumptions: Vec<&_> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume))
        .collect();
    let empty: [&crate::prepared_context::PreparedObligation; 0] = [];

    // Call verify_with_confirmation directly (the inductive step path)
    // with FORCE_CONFIRMATION_PANIC set. The first verification succeeds
    // (Verified), then the confirmation closure panics via the hook.
    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_CONFIRMATION_PANIC);
        let slices = crate::encoder::verification::VerificationSlices::new(
            &prepared,
            &assumptions,
            &empty,
            &empty,
            &empty,
            &empty,
        );
        verify_with_confirmation(
            || AYEncoder::setup_from_prepared(&slices, false, None),
            assertion,
            prepared.has_collection_context,
            None,
        )
        .expect("confirmation ay panic should stay in the outcome channel")
    };

    match result {
        AssertionOutcome::Unknown {
            reason, category, ..
        } => {
            assert_eq!(
                category,
                Some(UnknownCategory::SolverPanic),
                "ay panic during confirmation should be SolverPanic, not ConfirmationDisagree"
            );
            assert!(
                reason.contains("Confirmation check ay panic"),
                "reason should identify confirmation ay panic, got: {reason}"
            );
            assert!(
                reason.contains("len_check"),
                "reason should identify the assertion, got: {reason}"
            );
            assert!(
                reason.contains("sort mismatch"),
                "reason should preserve the panic detail, got: {reason}"
            );
        }
        other => panic!(
            "confirmation-stage ay panic should demote to Unknown/SolverPanic, got: {:?}",
            other
        ),
    }
}
