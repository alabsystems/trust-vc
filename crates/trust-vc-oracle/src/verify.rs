// trust-vc-oracle — Verification bridge (trust-vc-core → ProofFeedback)
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::{
    CounterexampleBinding, StepDiagnostic, StepResultKind, VerificationReport,
    VerificationReportOptions, VerifyResult,
};

use crate::feedback::{
    CertificateInfo, CounterexampleField, FailureLocalization, ProofFeedback, StepSummary,
    SubAssertionResult, SubAssertionStatus,
};

/// Convert a trust-vc-core `VerificationReport` into a `ProofFeedback`.
///
/// This is the translation layer that turns trust_vc's internal types into
/// the oracle's semantic feedback protocol. The key value-add is structuring
/// the information for LLM consumption.
pub(crate) fn report_to_feedback(report: &VerificationReport) -> ProofFeedback {
    let elapsed = report.total_elapsed();

    match report.result() {
        VerifyResult::Verified => {
            let steps = report.steps().iter().map(step_to_summary).collect();

            let certificate_info = extract_certificate_info(report);

            ProofFeedback::Verified {
                steps,
                elapsed,
                certificate_info,
            }
        }

        VerifyResult::Counterexample {
            obligation_name,
            model: _,
            bindings,
            ..
        } => {
            let counterexamples = bindings.iter().map(binding_to_field).collect();
            let localization = extract_localization(report);

            // Determine solver mode from the first non-verified step
            let solver_mode = report
                .first_non_verified_step()
                .and_then(|s| s.solver().map(|_| "default"))
                .unwrap_or("unknown")
                .to_string();

            ProofFeedback::Failed {
                counterexamples,
                localization,
                obligation_name: obligation_name.clone(),
                solver_mode,
                elapsed,
            }
        }

        // A model-less verification FAILURE, not an inconclusive result. It is
        // reported as `Failed` (the proof did not go through) with an EMPTY
        // `counterexamples` list — the emptiness is meaningful: no counterexample
        // was found, and none is invented for the oracle to reason from. Routing
        // it to `Unknown` instead would tell the oracle the run was merely
        // inconclusive and might succeed with more budget, which is false for a
        // permanent theory-incompleteness gap.
        VerifyResult::NotProved { reason, category } => ProofFeedback::Failed {
            counterexamples: Vec::new(),
            localization: extract_localization(report),
            obligation_name: format!("not proved (no model; {category:?}): {reason}"),
            solver_mode: report
                .first_non_verified_step()
                .and_then(|s| s.solver().map(|_| "default"))
                .unwrap_or("unknown")
                .to_string(),
            elapsed,
        },

        VerifyResult::Unknown { reason, category } => {
            let suggestion = category.actionable_suggestion().to_string();
            let is_retriable = category.is_retriable();

            ProofFeedback::Unknown {
                reason: reason.clone(),
                category: format!("{:?}", category),
                is_retriable,
                suggestion,
                elapsed,
            }
        }

        VerifyResult::Error { message } => ProofFeedback::Error {
            message: message.clone(),
        },

        other => ProofFeedback::Error {
            message: format!("Unexpected VerifyResult variant: {:?}", other),
        },
    }
}

fn binding_to_field(b: &CounterexampleBinding) -> CounterexampleField {
    CounterexampleField {
        name: b.display_name.clone(),
        ty: b.ty.clone(),
        value: b.value.clone(),
    }
}

fn step_to_summary(step: &StepDiagnostic) -> StepSummary {
    StepSummary {
        label: step.label().to_string(),
        phase: format!("{:?}", step.phase()),
        elapsed: step.elapsed(),
        result: match step.result() {
            StepResultKind::Verified => "verified".to_string(),
            StepResultKind::Counterexample => "counterexample".to_string(),
            StepResultKind::Unknown => "unknown".to_string(),
            StepResultKind::Error => "error".to_string(),
            StepResultKind::Skipped => "skipped".to_string(),
            _ => "unknown".to_string(),
        },
        used_assumptions: step.used_assumptions().to_vec(),
    }
}

fn step_result_to_status(kind: StepResultKind) -> SubAssertionStatus {
    match kind {
        StepResultKind::Verified => SubAssertionStatus::Pass,
        StepResultKind::Counterexample => SubAssertionStatus::Fail,
        StepResultKind::Unknown => SubAssertionStatus::Unknown,
        StepResultKind::Error => SubAssertionStatus::Error,
        StepResultKind::Skipped => SubAssertionStatus::Unknown,
        _ => SubAssertionStatus::Unknown,
    }
}

fn extract_localization(report: &VerificationReport) -> FailureLocalization {
    let sub_results: Vec<SubAssertionResult> = report
        .steps()
        .iter()
        .map(|step| SubAssertionResult {
            label: step.label().to_string(),
            status: step_result_to_status(step.result()),
        })
        .collect();

    FailureLocalization {
        full_assertion: None,
        sub_results,
    }
}

#[allow(unused_variables)]
fn extract_certificate_info(report: &VerificationReport) -> Option<CertificateInfo> {
    #[cfg(feature = "proof-certificates")]
    {
        report.proof().map(|cert| CertificateInfo {
            strict_verified: cert.strict_verified(),
            clean_supported: cert.clean_supported(),
            trust_count: cert.trust_count(),
            hole_count: cert.hole_count(),
            resolution_count: cert.resolution_count(),
            theory_count: cert.theory_count(),
        })
    }
    #[cfg(not(feature = "proof-certificates"))]
    {
        None
    }
}

/// Verify a set of obligations using the Proof builder API and return feedback.
///
/// This is the primary entry point for the oracle engine. It constructs
/// a verification context from the proposed annotations, runs ay, and
/// converts the result to `ProofFeedback`.
pub(crate) fn verify_with_annotations(
    function_name: &str,
    variables: &[(String, String)],
    requires: &[String],
    ensures: &[String],
) -> ProofFeedback {
    // No ensures means nothing to assert — trivially verified.
    if ensures.is_empty() {
        return ProofFeedback::Verified {
            steps: vec![],
            elapsed: std::time::Duration::ZERO,
            certificate_info: None,
        };
    }

    use trust_vc_core::verify::{Proof, Verifier};

    let mut proof = Proof::new(function_name);

    for (name, ty) in variables {
        proof = proof.with_variable(name, ty);
    }

    for req in requires {
        proof = proof.with_assumption(&format!("requires_{}", req.len()), req);
    }

    for ens in ensures {
        proof = proof.with_assertion(ens);
    }

    let options = VerificationReportOptions::new().with_verbose(true);
    let report = Verifier::verify_with_report(&proof, options);

    report_to_feedback(&report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_verify_simple_passing() {
        let feedback = verify_with_annotations(
            "test_positive",
            &[("x".to_string(), "u32".to_string())],
            &[],
            &["x >= 0".to_string()],
        );
        assert!(feedback.is_verified(), "u32 is always >= 0: {:?}", feedback);
    }

    #[test]
    fn test_verify_simple_failing() {
        let feedback = verify_with_annotations(
            "test_negative",
            &[("x".to_string(), "i32".to_string())],
            &[],
            &["x > 0".to_string()],
        );
        assert!(
            feedback.is_failed() || feedback.is_unknown(),
            "i32 is not always > 0: {:?}",
            feedback
        );
    }

    #[test]
    fn test_verify_with_precondition() {
        let feedback = verify_with_annotations(
            "test_precond",
            &[("x".to_string(), "i32".to_string())],
            &["x > 0".to_string()],
            &["x >= 1".to_string()],
        );
        assert!(
            feedback.is_verified(),
            "x > 0 implies x >= 1: {:?}",
            feedback
        );
    }

    #[test]
    fn test_feedback_json_roundtrip() {
        let feedback = ProofFeedback::Verified {
            steps: vec![StepSummary {
                label: "test".to_string(),
                phase: "Assertion".to_string(),
                elapsed: Duration::from_millis(42),
                result: "verified".to_string(),
                used_assumptions: vec![],
            }],
            elapsed: Duration::from_millis(42),
            certificate_info: None,
        };

        let json = feedback.to_json().unwrap();
        let parsed: ProofFeedback = serde_json::from_str(&json).unwrap();
        assert!(parsed.is_verified());
    }

    #[test]
    fn test_feedback_llm_summary_verified() {
        let feedback = ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::from_millis(15),
            certificate_info: None,
        };
        let summary = feedback.to_llm_summary();
        assert!(summary.contains("VERIFIED"));
    }

    #[test]
    fn test_feedback_llm_summary_failed() {
        let feedback = ProofFeedback::Failed {
            counterexamples: vec![CounterexampleField {
                name: "x".to_string(),
                ty: "i32".to_string(),
                value: "-5".to_string(),
            }],
            localization: FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ensures_positive".to_string(),
            solver_mode: "default".to_string(),
            elapsed: Duration::from_millis(10),
        };
        let summary = feedback.to_llm_summary();
        assert!(summary.contains("FAILED"));
        assert!(summary.contains("x: i32 = -5"));
    }
}
