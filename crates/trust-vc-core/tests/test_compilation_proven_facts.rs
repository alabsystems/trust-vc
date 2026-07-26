// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::compilation_proven_facts::{
    CompilationProvenFacts, CompilationProvenFactsError,
};
use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::{VerificationReportOptions, VerifyResult};

fn i32_ty() -> TrustVcType {
    TrustVcType::Int { width: 32 }
}

#[test]
fn test_compilation_proven_facts_extract_from_verified_report() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("index", i32_ty());
    ctx.declare_var_typed("capacity", i32_ty());
    ctx.declare_var_typed("divisor", i32_ty());

    ctx.push_obligation(ProofObligation::assume("index_nonnegative", "index >= 0"));
    ctx.push_obligation(ProofObligation::assume(
        "capacity_gt_index",
        "capacity > index",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "divisor_assumed_nonzero",
        "divisor != 0",
    ));

    ctx.push_obligation(ProofObligation::assert("bounds_check", "index < capacity"));
    ctx.push_obligation(ProofObligation::assert("divisor_nonzero", "divisor != 0"));
    ctx.push_obligation(ProofObligation::assert("overflow_free_add", "true"));
    ctx.push_obligation(ProofObligation::assert("dead_branch_else", "true"));

    let report = ctx.verify_with_report(VerificationReportOptions::new());
    assert!(
        matches!(report.result(), VerifyResult::Verified),
        "expected verified report, got {:?}",
        report.result()
    );

    let bounds_step = report
        .steps()
        .iter()
        .find(|step| step.label() == "bounds_check")
        .expect("report should include bounds_check");
    assert_eq!(bounds_step.condition(), Some("index < capacity"));

    let facts = CompilationProvenFacts::try_from_report(&report).expect("verified report");
    assert!(facts
        .bounds()
        .iter()
        .any(|fact| fact.step_label() == "bounds_check" && fact.condition() == "index < capacity"));
    assert!(facts
        .nonzero()
        .iter()
        .any(|fact| fact.step_label() == "divisor_nonzero"));
    assert!(facts
        .overflow_free()
        .iter()
        .any(|fact| fact.step_label() == "overflow_free_add"));
    assert!(facts
        .safe_indexing()
        .iter()
        .any(|fact| fact.step_label() == "bounds_check"));
    assert!(facts
        .dead_branches()
        .iter()
        .any(|fact| fact.step_label() == "dead_branch_else"));
}

#[test]
fn test_compilation_proven_facts_reject_non_verified_report() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("dead_branch_else", "false"));

    let report = ctx.verify_with_report(VerificationReportOptions::new());
    assert!(
        !matches!(report.result(), VerifyResult::Verified),
        "expected failing report, got {:?}",
        report.result()
    );

    let err = CompilationProvenFacts::try_from_report(&report).expect_err("must fail");
    assert_eq!(err, CompilationProvenFactsError::ReportNotVerified);
}
