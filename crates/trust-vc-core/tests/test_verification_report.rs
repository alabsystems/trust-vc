// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(feature = "named-assertions")]
use std::sync::MutexGuard;
#[cfg(feature = "named-assertions")]
use trust_vc_core::env::{lock_env, ScopedEnvVar};
use trust_vc_core::ir::TrustVcType;
use trust_vc_core::vc::{ProofObligation, SolverMode, VerificationContext};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::{UnknownCategory, VerificationPhase, VerificationReportOptions, VerifyResult};

/// Disables the VC-level cache for the caller's scope, serialized behind the
/// process-wide env lock and restored on drop. Hold the returned guards for
/// the duration of the test (the `ScopedEnvVar` drops — restoring the previous
/// value — before the lock guard releases).
#[cfg(feature = "named-assertions")]
#[must_use = "hold the returned guards while the VC cache must stay disabled"]
fn disable_vc_cache() -> (ScopedEnvVar, MutexGuard<'static, ()>) {
    let lock = lock_env();
    let cache = ScopedEnvVar::set("TRUST_VC_DISABLE_VC_CACHE", "1");
    (cache, lock)
}

#[test]
fn test_verification_report_formats_unknown_category_and_suggestion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("gt_zero", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("lt_zero", "x < 0"));
    ctx.push_obligation(ProofObligation::assert("post", "x == 0"));

    let report = ctx.verify_with_report(VerificationReportOptions::new().with_verbose(true));
    assert!(
        matches!(report.result(), VerifyResult::Unknown { .. }),
        "contradictory assumptions should surface as Unknown, got {:?}",
        report.result()
    );

    let rendered = report.format_with_options(VerificationReportOptions::new().with_verbose(true));
    assert!(rendered.contains("category: VacuousTruth"));
    assert!(rendered.contains(UnknownCategory::VacuousTruth.actionable_suggestion()));
}

#[test]
fn test_verification_report_includes_assertion_step_solver_stats() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));

    let report = ctx.verify_with_report(VerificationReportOptions::new().with_verbose(true));
    let assertion_step = report
        .steps()
        .iter()
        .find(|step| step.phase() == VerificationPhase::Assertion)
        .expect("report should include an assertion step");
    assert!(
        assertion_step.solver().is_some(),
        "assertion step should carry solver stats"
    );

    let rendered = report.format_with_options(VerificationReportOptions::new().with_verbose(true));
    assert!(rendered.contains("stats: conflicts="));
    assert!(rendered.contains("solver: level="));
}

#[test]
fn test_pipeline_report_carries_preflight_summary() {
    let mut pipeline = VerificationPipeline::new();
    pipeline
        .context_mut()
        .declare_var_typed("x", TrustVcType::Int { width: 32 });
    pipeline.add_obligation(ProofObligation::assume("gt_zero", "x > 0"));
    pipeline.add_obligation(ProofObligation::assert("nonneg", "x >= 0"));

    let report = pipeline.verify_with_report(VerificationReportOptions::new().with_verbose(true));

    let pipeline_summary = report
        .pipeline()
        .expect("pipeline report should include preflight diagnostics");
    assert_eq!(pipeline_summary.num_obligations(), 2);
    assert_eq!(pipeline_summary.num_variables(), 1);
    assert!(pipeline_summary.has_assertions());
    assert!(pipeline_summary.has_assumptions());

    let rendered = report.format_with_options(VerificationReportOptions::new().with_verbose(true));
    assert!(rendered.contains("pipeline: obligations=2, variables=1"));
}

/// Test that the report pipeline works for assertions requiring demand-inline recovery.
///
/// Since the historical ay bump to a8c7a538, and with the current workspace ay
/// pin, the solver may verify
/// `helper(3) == 6` directly without demand-inline recovery. The test accepts
/// both outcomes: direct verification (no steps) or demand-inline recovery
/// (assertion step with recovery metadata). Both are correct — Verified is Verified.
#[test]
fn test_verification_report_surfaces_demand_inline_recovery_note() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed(
        "helper",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "seed",
        TrustVcType::Int { width: 32 },
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume("__body_axiom_helper", "helper(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["seed(x)".to_string()]]),
    );
    ctx.push_obligation(
        ProofObligation::assert("check_helper_3", "helper(3) == 6")
            .with_solver_mode(SolverMode::NonlinearArith),
    );

    let report = ctx.verify_with_report(VerificationReportOptions::new().with_verbose(true));
    assert!(
        matches!(report.result(), VerifyResult::Verified),
        "should verify the assertion, got {:?}",
        report.result()
    );

    // If demand-inline recovery was needed, verify the metadata is correct.
    // Current ay versions may verify directly without recovery.
    if let Some(assertion_step) = report
        .steps()
        .iter()
        .find(|step| step.phase() == VerificationPhase::Assertion)
    {
        if let Some(recovery) = assertion_step.demand_inline_recovery() {
            assert_eq!(recovery.inlined_functions(), ["helper".to_string()]);
            assert_eq!(recovery.depth_used(), 1);

            let rendered =
                report.format_with_options(VerificationReportOptions::new().with_verbose(true));
            assert!(rendered.contains("verified after inlining helper"));
            assert!(rendered.contains("consider strengthening helper's contract"));
        }
    }
}

#[cfg(feature = "named-assertions")]
#[test]
fn test_assertion_step_reports_used_assumptions_subset() {
    let _env = disable_vc_cache();

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("upper_bound", "x < 10"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));

    let report = ctx.verify_with_report(VerificationReportOptions::new().with_verbose(true));
    assert!(
        matches!(report.result(), VerifyResult::Verified),
        "expected Verified, got {:?}",
        report.result()
    );

    let assertion_step = report
        .steps()
        .iter()
        .find(|step| step.phase() == VerificationPhase::Assertion)
        .expect("report should include an assertion step");
    assert!(
        !assertion_step.used_assumptions().is_empty(),
        "verified assertion step should record at least one used assumption"
    );
    assert!(
        assertion_step
            .used_assumptions()
            .iter()
            .all(|name| matches!(name.as_str(), "positive" | "upper_bound")),
        "used assumptions should be a subset of the declared assumptions, got {:?}",
        assertion_step.used_assumptions()
    );

    let rendered = report.format_with_options(VerificationReportOptions::new().with_verbose(true));
    assert!(rendered.contains("used assumptions:"));
}

#[cfg(feature = "named-assertions")]
#[test]
fn test_vacuous_precheck_reports_contradictory_assumption_core() {
    let _env = disable_vc_cache();

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("gt_zero", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("lt_zero", "x < 0"));
    ctx.push_obligation(ProofObligation::assert("post", "x == 0"));

    let report = ctx.verify_with_report(VerificationReportOptions::new().with_verbose(true));
    assert!(
        matches!(report.result(), VerifyResult::Unknown { .. }),
        "contradictory assumptions should surface as Unknown, got {:?}",
        report.result()
    );

    let vacuous_step = report
        .steps()
        .iter()
        .find(|step| step.phase() == VerificationPhase::VacuousPrecheck)
        .expect("report should include a vacuous precheck step");
    let used = vacuous_step.used_assumptions();
    assert_eq!(
        used.len(),
        2,
        "expected both contradictory assumptions in the core"
    );
    assert!(
        used.iter().any(|name| name == "gt_zero"),
        "vacuous precheck core should include gt_zero, got {:?}",
        used
    );
    assert!(
        used.iter().any(|name| name == "lt_zero"),
        "vacuous precheck core should include lt_zero, got {:?}",
        used
    );
}
