//! Proof coverage tests for vacuous.rs
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers previously untested production paths: empty-assumption early return,
//! contradictory-assumption detection (Unsat → Unknown), satisfiable-assumption
//! pass-through, demoted_context_result formatting, and int-mode dual-pass
//! scheduling via obligation_uses_int_mode.
//!
//! Wiring: Worker must add to vacuous.rs:
//!   #[cfg(test)]
//!   #[path = "vacuous_proof_tests.rs"]
//!   mod proof_tests;
//!
//! Part of #949.

use super::*;
use crate::encoder::diagnostics::{EncodingApproximation, EncodingDiagnostics};
use crate::encoder::types::VerifyResult;
use crate::ir::TrustVcType;
use crate::prepared_context::prepare_context;
use crate::vc::{ObligationKind, ProofObligation, VerificationContext};

// -- Helper to build a prepared context with typed variables and obligations --

fn build_prepared(
    vars: &[(&str, TrustVcType)],
    obligations: &[ProofObligation],
) -> crate::prepared_context::PreparedVerificationContext {
    let mut ctx = VerificationContext::new();
    for (name, ty) in vars {
        ctx.declare_var_typed(name, ty.clone());
    }
    for obligation in obligations {
        ctx.push_obligation(obligation.clone());
    }
    prepare_context(&ctx).expect("prepare_context should succeed for test fixture")
}

// -- check_vacuous_truth: empty assumptions early return --

#[test]
fn check_vacuous_truth_returns_none_when_no_assumptions() {
    let prepared = build_prepared(
        &[("x", TrustVcType::Int { width: 32 })],
        &[ProofObligation::assert("test", "x == x")],
    );
    let mut diag = EncodingDiagnostics::default();
    let result = check_vacuous_truth(&prepared, &[], &[], &mut diag);
    assert!(
        result.is_none(),
        "empty assumptions should return None (no vacuity possible)"
    );
}

#[test]
fn check_vacuous_truth_returns_none_when_both_slices_empty() {
    let prepared = build_prepared(
        &[("y", TrustVcType::Uint { width: 64 })],
        &[ProofObligation::assert("trivial", "true")],
    );
    let empty_assumptions: Vec<&crate::prepared_context::PreparedObligation> = vec![];
    let empty_broadcasts: Vec<&crate::prepared_context::PreparedObligation> = vec![];
    let mut diag = EncodingDiagnostics::default();
    let result = check_vacuous_truth(&prepared, &empty_assumptions, &empty_broadcasts, &mut diag);
    assert!(
        result.is_none(),
        "both slices empty should hit the early return None path"
    );
}

// -- check_vacuous_truth: contradictory assumptions detected (Unsat → Unknown) --

#[test]
fn check_vacuous_truth_detects_contradictory_assumptions() {
    let prepared = build_prepared(
        &[("x", TrustVcType::Int { width: 32 })],
        &[
            ProofObligation::assume("high", "x > 100"),
            ProofObligation::assume("low", "x < 0"),
            ProofObligation::assert("dummy", "x == x"),
        ],
    );
    let assumptions: Vec<&_> = prepared
        .obligations
        .iter()
        .filter(|o| o.kind == ObligationKind::Assume)
        .collect();
    let mut diag = EncodingDiagnostics::default();
    let result = check_vacuous_truth(&prepared, &assumptions, &[], &mut diag);
    assert!(
        result.is_some(),
        "contradictory assumptions (x > 100 AND x < 0) should be detected as vacuous"
    );
    match result.unwrap() {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("contradictory") || reason.contains("vacuous"),
                "unknown reason should mention contradictory/vacuous, got: {}",
                reason
            );
        }
        other => panic!(
            "expected VerifyResult::Unknown for vacuous truth, got: {:?}",
            other
        ),
    }
}

// -- check_vacuous_truth: satisfiable assumptions pass through --

#[test]
fn check_vacuous_truth_returns_none_when_assumptions_satisfiable() {
    let prepared = build_prepared(
        &[("x", TrustVcType::Int { width: 32 })],
        &[
            ProofObligation::assume("positive", "x > 0"),
            ProofObligation::assert("dummy", "x == x"),
        ],
    );
    let assumptions: Vec<&_> = prepared
        .obligations
        .iter()
        .filter(|o| o.kind == ObligationKind::Assume)
        .collect();
    let mut diag = EncodingDiagnostics::default();
    let result = check_vacuous_truth(&prepared, &assumptions, &[], &mut diag);
    assert!(
        result.is_none(),
        "satisfiable assumption (x > 0) should not trigger vacuous truth detection"
    );
}

// -- demoted_context_result: formatting --

#[test]
fn demoted_context_result_produces_unknown_with_demotion_prefix() {
    let mut diag = EncodingDiagnostics::default();
    diag.record(EncodingApproximation::FunctionContextReturnTypeOmitted);
    let result = demoted_context_result("test_target", &diag);
    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.starts_with("demoted:"),
                "demoted_context_result should produce a reason starting with 'demoted:', got: {}",
                reason
            );
            assert!(
                reason.contains("test_target"),
                "demoted_context_result should include the target name, got: {}",
                reason
            );
        }
        other => panic!(
            "demoted_context_result should produce Unknown, got: {:?}",
            other
        ),
    }
}

#[test]
fn demoted_context_result_with_no_demoting_still_formats() {
    let diag = EncodingDiagnostics::default();
    let result = demoted_context_result("empty_diag_target", &diag);
    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("empty_diag_target"),
                "should still include target name even with no demoting categories"
            );
        }
        other => panic!(
            "demoted_context_result should produce Unknown, got: {:?}",
            other
        ),
    }
}

// -- obligation_uses_int_mode: tested indirectly via dual-pass scheduling --
// obligation_uses_int_mode is private, but its behavior determines whether
// the BV-only pass is followed by an int-mode pass. We test this by including
// a MeasureDecreases obligation which triggers int-mode, and verifying that
// the vacuous check still returns None for satisfiable assumptions.

#[test]
fn check_vacuous_truth_handles_int_mode_scheduling_with_measure_obligation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Uint { width: 64 });
    ctx.push_obligation(ProofObligation::assume("pos", "x > 0"));
    // MeasureDecreases triggers int-mode path in obligation_uses_int_mode
    ctx.push_obligation(ProofObligation::measure_decreases("measure", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("dummy", "true"));

    let prepared = prepare_context(&ctx).expect("prepare should succeed");
    let assumptions: Vec<&_> = prepared
        .obligations
        .iter()
        .filter(|o| o.kind == ObligationKind::Assume)
        .collect();
    let mut diag = EncodingDiagnostics::default();
    let result = check_vacuous_truth(&prepared, &assumptions, &[], &mut diag);
    assert!(
        result.is_none(),
        "satisfiable assumptions should pass through even with int-mode (MeasureDecreases) present"
    );
}

// -- catch_unwind path --
// The catch_unwind wraps run_vacuous_precheck to gracefully handle ay-dpll
// panics during assumption encoding. We cannot easily trigger a ay panic
// from outside, but we can verify the function doesn't propagate panics
// for complex expressions that might stress the encoder.

#[test]
fn check_vacuous_truth_does_not_panic_with_complex_assumptions() {
    let prepared = build_prepared(
        &[
            ("a", TrustVcType::Int { width: 32 }),
            ("b", TrustVcType::Int { width: 32 }),
            ("c", TrustVcType::Uint { width: 64 }),
        ],
        &[
            ProofObligation::assume("bound_a", "a > 0"),
            ProofObligation::assume("bound_b", "b < 100"),
            ProofObligation::assume("bound_c", "c > 0"),
            ProofObligation::assume("relate", "a + b > 50"),
            ProofObligation::assert("dummy", "true"),
        ],
    );
    let assumptions: Vec<&_> = prepared
        .obligations
        .iter()
        .filter(|o| o.kind == ObligationKind::Assume)
        .collect();
    let mut diag = EncodingDiagnostics::default();
    // Should not panic — catch_unwind protects against internal errors
    let result = check_vacuous_truth(&prepared, &assumptions, &[], &mut diag);
    assert!(
        result.is_none(),
        "multiple satisfiable assumptions should pass through without panic"
    );
}
