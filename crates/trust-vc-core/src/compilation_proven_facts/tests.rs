// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::*;
use crate::verification_report::VerificationReport;

fn make_step(
    phase: VerificationPhase,
    label: &str,
    condition: Option<&str>,
    result: StepResultKind,
) -> StepDiagnostic {
    if result == StepResultKind::Skipped {
        return StepDiagnostic::pending_with_condition(
            phase,
            label.to_string(),
            None,
            condition.map(str::to_string),
        );
    }

    StepDiagnostic::from_verify_result_with_condition(
        phase,
        label.to_string(),
        None,
        condition.map(str::to_string),
        Duration::from_millis(5),
        &match result {
            StepResultKind::Verified => VerifyResult::Verified,
            StepResultKind::Counterexample => VerifyResult::Counterexample {
                obligation_name: label.to_string(),
                location: None,
                model: None,
                bindings: Vec::new(),
            },
            StepResultKind::NotProved => VerifyResult::unknown(
                "incompleteness",
                Some(crate::UnknownCategory::Incompleteness),
            ),
            StepResultKind::Unknown => {
                VerifyResult::unknown("timeout", Some(crate::UnknownCategory::Timeout))
            }
            StepResultKind::Error => VerifyResult::Error {
                message: "error".to_string(),
            },
            StepResultKind::Skipped => unreachable!("handled above"),
        },
    )
}

fn make_report(result: VerifyResult, steps: Vec<StepDiagnostic>) -> VerificationReport {
    VerificationReport::from_parts(result, None, steps, Duration::from_millis(25))
}

#[test]
fn test_try_from_report_extracts_all_compilation_categories() {
    let report = make_report(
        VerifyResult::Verified,
        vec![
            make_step(
                VerificationPhase::Assertion,
                "bounds_check",
                Some("index < capacity"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::Assertion,
                "divisor_nonzero",
                Some("divisor != 0"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::Assertion,
                "sum_safe",
                Some("no_overflow(x + y)"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::LoopInvariant,
                "safe_indexing_loop",
                Some("idx < data.len()"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::Assertion,
                "dead_branch_guard",
                Some("false"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::ParallelProof,
                "parallel_bounds",
                Some("index < capacity"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::Assertion,
                "overflow_skipped",
                Some("no_overflow(z)"),
                StepResultKind::Skipped,
            ),
            make_step(
                VerificationPhase::Assertion,
                "overflow_failed",
                Some("no_overflow(w)"),
                StepResultKind::Counterexample,
            ),
        ],
    );

    let facts = CompilationProvenFacts::try_from_report(&report).expect("verified report");
    assert_eq!(facts.bounds().len(), 2);
    assert_eq!(facts.nonzero().len(), 1);
    assert_eq!(facts.overflow_free().len(), 1);
    assert_eq!(facts.safe_indexing().len(), 2);
    assert_eq!(facts.dead_branches().len(), 1);
    assert_eq!(facts.bounds()[0].condition(), "index < capacity");
    assert_eq!(facts.safe_indexing()[1].condition(), "idx < data.len()");
}

#[test]
fn test_try_from_report_falls_back_to_step_label() {
    let report = make_report(
        VerifyResult::Verified,
        vec![make_step(
            VerificationPhase::Assertion,
            "overflow_free_add",
            None,
            StepResultKind::Verified,
        )],
    );

    let facts = CompilationProvenFacts::try_from_report(&report).expect("verified report");
    assert_eq!(facts.overflow_free().len(), 1);
    assert_eq!(facts.overflow_free()[0].condition(), "overflow_free_add");
}

#[test]
fn test_try_from_report_rejects_non_verified_reports() {
    let report = make_report(
        VerifyResult::Counterexample {
            obligation_name: "bad".to_string(),
            location: None,
            model: None,
            bindings: Vec::new(),
        },
        vec![make_step(
            VerificationPhase::Assertion,
            "dead_branch_guard",
            Some("false"),
            StepResultKind::Counterexample,
        )],
    );

    let err = CompilationProvenFacts::try_from_report(&report).expect_err("must fail");
    assert_eq!(err, CompilationProvenFactsError::ReportNotVerified);
}

#[test]
fn test_to_json_exports_counts_and_buckets() {
    let report = make_report(
        VerifyResult::Verified,
        vec![
            make_step(
                VerificationPhase::Assertion,
                "bounds_check",
                Some("index < capacity"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::Assertion,
                "divisor_nonzero",
                Some("divisor != 0"),
                StepResultKind::Verified,
            ),
        ],
    );

    let facts = CompilationProvenFacts::try_from_report(&report).expect("verified report");
    let json = facts.to_json();
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("must produce valid json");

    assert_eq!(parsed["counts"]["bounds"], 1);
    assert_eq!(parsed["counts"]["nonzero"], 1);
    assert_eq!(parsed["counts"]["total_matches"], 3);
    assert_eq!(parsed["bounds"][0]["condition"], "index < capacity");
    assert_eq!(parsed["nonzero"][0]["phase"], "assertion");
}
