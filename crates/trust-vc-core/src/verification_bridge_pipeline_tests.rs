//! Pipeline-focused verification bridge tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::parallel::with_parallel_verify_override;
use super::*;
use crate::encoder::tests::{expect_counterexample, expect_error_containing, expect_verified};

#[test]
fn test_empty_pipeline_verifies() {
    // Empty context cannot be verified - this is correct behavior to prevent
    // vacuous proofs. The encoder properly returns an error for empty context.
    let pipeline = VerificationPipeline::new();
    let result = pipeline.verify();
    expect_error_containing(&result, "empty context", "empty pipeline");
}

#[test]
fn test_pipeline_with_valid_assertion() {
    let mut pipeline = VerificationPipeline::new();
    pipeline.add_obligation(ProofObligation::assert("test", "5 > 3"));

    let result = pipeline.verify();
    expect_verified(&result, "");
}

#[test]
fn test_pipeline_seq_from_fn_len_and_index() {
    let mut pipeline = VerificationPipeline::new();
    pipeline.add_obligation(ProofObligation::assert(
        "seq_from_fn_len",
        "trust_vc_types::Seq::<i32>::from_fn(3usize, SpecFn::new(|i: usize| i as i32)).len() == 3usize",
    ));
    pipeline.add_obligation(ProofObligation::assert(
        "seq_from_fn_index",
        "trust_vc_types::Seq::<i32>::from_fn(3usize, SpecFn::new(|i: usize| i as i32)).index(2usize) == 2i32",
    ));

    let result = pipeline.verify();
    expect_verified(&result, "Seq::from_fn length and guarded index axiom");
}

#[test]
fn test_pipeline_seq_new_generator_alias_len_and_index() {
    let mut pipeline = VerificationPipeline::new();
    pipeline.add_obligation(ProofObligation::assert(
        "seq_new_generator_len",
        "trust_vc_types::Seq::<i32>::new(3usize, SpecFn::new(|i: usize| i as i32)).len() == 3usize",
    ));
    pipeline.add_obligation(ProofObligation::assert(
        "seq_new_generator_index",
        "trust_vc_types::Seq::<i32>::new(3usize, SpecFn::new(|i: usize| i as i32)).index(2usize) == 2i32",
    ));

    let result = pipeline.verify();
    expect_verified(
        &result,
        "Seq::new(len, generator) alias length and guarded index axiom",
    );
}

#[test]
fn test_pipeline_with_invalid_assertion() {
    let mut pipeline = VerificationPipeline::new();
    pipeline.add_obligation(ProofObligation::assert("test", "3 > 5"));

    let result = pipeline.verify();
    expect_counterexample(&result, "");
}

#[test]
fn test_pipeline_diagnostic() {
    let mut pipeline = VerificationPipeline::new();
    pipeline.add_obligation(ProofObligation::assert("test1", "true"));
    pipeline.add_obligation(ProofObligation::assume("test2", "x > 0"));

    let diagnostic = pipeline.diagnose();
    assert_eq!(diagnostic.num_obligations(), 2);
    assert!(diagnostic.has_assertions());
    assert!(diagnostic.has_assumptions());
}

#[cfg(feature = "ty")]
#[test]
fn test_pipeline_clear_clears_protocol_obligations() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .protocol_obligations
        .push(test_protocol_obligation("PipelineClear"));

    assert_eq!(pipeline.protocol_obligations.len(), 1);
    assert_eq!(pipeline.diagnose().num_obligations(), 1);

    pipeline.clear();

    assert!(pipeline.protocol_obligations.is_empty());
    assert_eq!(pipeline.diagnose().num_obligations(), 0);
}

#[cfg(feature = "ty")]
#[test]
fn test_pipeline_diagnostic_counts_protocol_obligations() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .protocol_obligations
        .push(test_protocol_obligation("PipelineDiagnose"));

    let diagnostic = pipeline.diagnose();
    assert_eq!(diagnostic.num_obligations(), 1);
    assert!(!diagnostic.has_assertions());
    assert!(!diagnostic.has_assumptions());
}

#[test]
fn test_parallel_override_enables_parallel_report_steps() {
    with_cleared_registrations(|| {
        register_proof(
            "proof_a",
            vec![ProofObligation::assert("check_a", "1 + 1 == 2")],
        );
        register_proof(
            "proof_b",
            vec![ProofObligation::assert("check_b", "2 + 2 == 4")],
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let report = with_parallel_verify_override(true, || {
            pipeline.verify_with_report(VerificationReportOptions::new())
        });

        expect_verified(report.result(), "parallel override report");
        assert_eq!(
            report.steps().len(),
            2,
            "parallel path should emit one step per proof"
        );
        assert!(
            report
                .steps()
                .iter()
                .all(|step| step.phase() == VerificationPhase::ParallelProof),
            "parallel override should force ParallelProof steps, got {:?}",
            report.steps()
        );
        assert_eq!(
            report
                .steps()
                .iter()
                .map(|step| step.label())
                .collect::<Vec<_>>(),
            vec!["proof_a", "proof_b"],
            "parallel report should preserve registered proof names",
        );
    });
}

#[test]
fn test_parallel_override_false_uses_assertion_report_steps() {
    with_cleared_registrations(|| {
        register_proof(
            "proof_a",
            vec![ProofObligation::assert("check_a", "1 + 1 == 2")],
        );
        register_proof(
            "proof_b",
            vec![ProofObligation::assert("check_b", "2 + 2 == 4")],
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let report = with_parallel_verify_override(false, || {
            pipeline.verify_with_report(VerificationReportOptions::new())
        });

        expect_verified(report.result(), "non-parallel override report");
        assert!(
            report
                .steps()
                .iter()
                .all(|step| step.phase() != VerificationPhase::ParallelProof),
            "disabled override should stay on the ordinary assertion path, got {:?}",
            report.steps()
        );
        assert!(
            report
                .steps()
                .iter()
                .any(|step| step.phase() == VerificationPhase::Assertion),
            "disabled override should keep assertion-phase reporting",
        );
    });
}

#[test]
fn test_pipeline_diagnostic_display_renders_full_summary() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    pipeline.add_obligation(ProofObligation::assert("check1", "x > 0"));
    pipeline.add_obligation(ProofObligation::assume("premise1", "x == 5"));

    let diag = pipeline.diagnose();
    let display = diag.to_string();

    assert!(
        display.contains("2 obligations"),
        "Display should show obligation count, got: {display}"
    );
    assert!(
        display.contains("1 variables"),
        "Display should show variable count, got: {display}"
    );
    assert!(
        display.contains("assertions=true"),
        "Display should show assertions=true, got: {display}"
    );
    assert!(
        display.contains("assumptions=true"),
        "Display should show assumptions=true, got: {display}"
    );
}

#[test]
fn test_pipeline_clear_resets_diagnostic_state_and_collection_error() {
    let mut pipeline = VerificationPipeline::new();

    // Populate: variable, assertion, assumption, and a collection_error
    pipeline
        .context_mut()
        .declare_var_typed("a", crate::ir::TrustVcType::Bool);
    pipeline.add_obligation(ProofObligation::assert("assert1", "a == true"));
    pipeline.add_obligation(ProofObligation::assume("assume1", "a"));
    pipeline.collection_error = Some(TrustVcError::Internal {
        context: "test",
        detail: "synthetic error".to_string(),
    });

    // Pre-clear: verify non-empty state
    let diag_before = pipeline.diagnose();
    assert_eq!(diag_before.num_obligations(), 2);
    assert_eq!(diag_before.num_variables(), 1);
    assert!(diag_before.has_assertions());
    assert!(diag_before.has_assumptions());
    assert!(pipeline.collection_error.is_some());

    let display_before = diag_before.to_string();
    assert!(
        display_before.contains("2 obligations"),
        "pre-clear Display should show 2 obligations, got: {display_before}"
    );

    // Clear
    pipeline.clear();

    // Post-clear: verify empty state
    assert!(
        pipeline.context().obligations().is_empty(),
        "clear() must empty obligations"
    );
    assert!(
        pipeline.context().variables().is_empty(),
        "clear() must empty variables"
    );
    assert!(
        pipeline.collection_error.is_none(),
        "clear() must reset collection_error to None"
    );

    let diag_after = pipeline.diagnose();
    assert_eq!(diag_after.num_obligations(), 0);
    assert_eq!(diag_after.num_variables(), 0);
    assert!(!diag_after.has_assertions());
    assert!(!diag_after.has_assumptions());

    let display_after = diag_after.to_string();
    assert!(
        display_after.contains("0 obligations"),
        "post-clear Display should show 0 obligations, got: {display_after}"
    );
    assert!(
        display_after.contains("0 variables"),
        "post-clear Display should show 0 variables, got: {display_after}"
    );
    assert!(
        display_after.contains("assertions=false"),
        "post-clear Display should show assertions=false, got: {display_after}"
    );
    assert!(
        display_after.contains("assumptions=false"),
        "post-clear Display should show assumptions=false, got: {display_after}"
    );
}
