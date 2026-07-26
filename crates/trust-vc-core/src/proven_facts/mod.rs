//! Extraction of proven facts from verification reports for compilation hints.
//!
//! When a verification report shows that certain assertions, preconditions,
//! postconditions, or invariants were proven, this module extracts structured
//! `ProvenFact` records. Downstream consumers (e.g., a compiler backend) can
//! use these to emit `unreachable_unchecked()` on provably-false branches or
//! other optimization hints.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

pub mod extraction;
pub mod hints;
pub mod report;

use serde::{Deserialize, Serialize};

use crate::verification_report::{StepResultKind, VerificationPhase, VerificationReport};

pub use extraction::{AssertionFact, ProofStatus, ProvenFacts};
pub use hints::{emit_hint_annotations, generate_hints, OptimizationHint, OptimizationHintKind};
pub use report::{format_report, to_json, ProvenFactsReport};

/// Classification of a proven fact by its origin in the proof surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProvenFactKind {
    /// A user-written `assert!` or `assert_by!` that the solver verified.
    Assertion,
    /// A `requires!` clause proven at a call site.
    Precondition,
    /// An `ensures!` clause proven at function exit.
    Postcondition,
    /// A loop `invariant!` proven to hold across iterations.
    Invariant,
}

impl std::fmt::Display for ProvenFactKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::Assertion => "assertion",
            Self::Precondition => "precondition",
            Self::Postcondition => "postcondition",
            Self::Invariant => "invariant",
        };
        write!(f, "{label}")
    }
}

/// A single fact proven by the verification engine.
///
/// Carries enough information for a downstream compiler to locate the
/// corresponding branch in the source and emit optimization hints (e.g.,
/// `unreachable_unchecked()` on the negation branch).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ProvenFact {
    /// What kind of proof obligation produced this fact.
    kind: ProvenFactKind,
    /// The expression string as it appeared in the verification condition
    /// (e.g., `"x > 0"`, `"result == old(seq).len()"`).
    expression: String,
    /// Source location string if available (e.g., `"src/lib.rs:42:5"`).
    source_location: Option<String>,
    /// The verification step label from the report.
    step_label: String,
}

impl ProvenFact {
    /// Creates a new proven fact.
    #[must_use]
    pub fn new(
        kind: ProvenFactKind,
        expression: impl Into<String>,
        source_location: Option<String>,
        step_label: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            expression: expression.into(),
            source_location,
            step_label: step_label.into(),
        }
    }

    /// The kind of proof obligation that produced this fact.
    #[must_use]
    pub const fn kind(&self) -> ProvenFactKind {
        self.kind
    }

    /// The expression string from the verification condition.
    #[must_use]
    pub fn expression(&self) -> &str {
        &self.expression
    }

    /// Source location, if available.
    #[must_use]
    pub fn source_location(&self) -> Option<&str> {
        self.source_location.as_deref()
    }

    /// The step label from the verification report.
    #[must_use]
    pub fn step_label(&self) -> &str {
        &self.step_label
    }
}

/// Maps a `VerificationPhase` to a `ProvenFactKind`.
///
/// Returns `None` for phases that do not directly map to an optimization-
/// relevant proven fact (e.g., `VacuousPrecheck`, `ParallelProof`).
#[must_use]
fn phase_to_fact_kind(phase: VerificationPhase) -> Option<ProvenFactKind> {
    match phase {
        VerificationPhase::Assertion | VerificationPhase::AssertBy => {
            Some(ProvenFactKind::Assertion)
        }
        VerificationPhase::Recommendation => Some(ProvenFactKind::Precondition),
        VerificationPhase::LoopEnsures => Some(ProvenFactKind::Postcondition),
        VerificationPhase::LoopInvariant | VerificationPhase::LoopInvariantInductiveStep => {
            Some(ProvenFactKind::Invariant)
        }
        // VacuousPrecheck and ParallelProof are meta-steps, not user-facing facts.
        _ => None,
    }
}

/// Extracts proven facts from a verification report.
///
/// Only steps that completed with `StepResultKind::Verified` are extracted.
/// Steps that are skipped, unknown, errored, or produce counterexamples are
/// excluded.
///
/// # Examples
///
/// ```no_run
/// use trust_vc_core::proven_facts::extract_proven_facts;
/// use trust_vc_core::VerificationReport;
///
/// fn use_proven_facts(report: &VerificationReport) {
///     let facts = extract_proven_facts(report);
///     for fact in &facts {
///         println!("{}: {} at {:?}", fact.kind(), fact.expression(), fact.source_location());
///     }
/// }
/// ```
#[must_use]
pub fn extract_proven_facts(report: &VerificationReport) -> Vec<ProvenFact> {
    report
        .steps()
        .iter()
        .filter(|step| step.result() == StepResultKind::Verified)
        .filter_map(|step| {
            let kind = phase_to_fact_kind(step.phase())?;
            Some(ProvenFact {
                kind,
                expression: step.label().to_string(),
                source_location: step.location().map(str::to_string),
                step_label: step.label().to_string(),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;
    use crate::verification_report::{StepResultKind, VerificationPhase, VerificationReport};
    use crate::VerifyResult;

    /// Helper: build a `StepDiagnostic` with the given phase, label, location,
    /// and result kind.
    fn make_step(
        phase: VerificationPhase,
        label: &str,
        location: Option<&str>,
        result: StepResultKind,
    ) -> crate::verification_report::StepDiagnostic {
        // Skipped steps use `pending()` directly because there is no
        // `VerifyResult::Skipped` variant — `from_verify_result` would
        // map `VerifyResult::Verified` to `StepResultKind::Verified`.
        if result == StepResultKind::Skipped {
            return crate::verification_report::StepDiagnostic::pending(
                phase,
                label.to_string(),
                location.map(str::to_string),
            );
        }

        crate::verification_report::StepDiagnostic::from_verify_result(
            phase,
            label.to_string(),
            location.map(str::to_string),
            Duration::from_millis(5),
            &match result {
                StepResultKind::Verified => VerifyResult::Verified,
                StepResultKind::Counterexample => VerifyResult::Counterexample {
                    obligation_name: label.to_string(),
                    model: None,
                    bindings: Vec::new(),
                },
                // Built through the same funnel that enforces the split, so
                // this arm exercises the real routing rather than mimicking it.
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

    fn make_report(steps: Vec<crate::verification_report::StepDiagnostic>) -> VerificationReport {
        VerificationReport::from_parts(
            VerifyResult::Verified,
            None,
            steps,
            Duration::from_millis(100),
        )
    }

    // -- ProvenFactKind tests --

    #[test]
    fn test_proven_fact_kind_display_assertion() {
        assert_eq!(ProvenFactKind::Assertion.to_string(), "assertion");
    }

    #[test]
    fn test_proven_fact_kind_display_precondition() {
        assert_eq!(ProvenFactKind::Precondition.to_string(), "precondition");
    }

    #[test]
    fn test_proven_fact_kind_display_postcondition() {
        assert_eq!(ProvenFactKind::Postcondition.to_string(), "postcondition");
    }

    #[test]
    fn test_proven_fact_kind_display_invariant() {
        assert_eq!(ProvenFactKind::Invariant.to_string(), "invariant");
    }

    // -- ProvenFact constructor and accessor tests --

    #[test]
    fn test_proven_fact_new_with_location() {
        let fact = ProvenFact::new(
            ProvenFactKind::Assertion,
            "x > 0",
            Some("src/lib.rs:42:5".to_string()),
            "nonneg_check",
        );
        assert_eq!(fact.kind(), ProvenFactKind::Assertion);
        assert_eq!(fact.expression(), "x > 0");
        assert_eq!(fact.source_location(), Some("src/lib.rs:42:5"));
        assert_eq!(fact.step_label(), "nonneg_check");
    }

    #[test]
    fn test_proven_fact_new_without_location() {
        let fact = ProvenFact::new(
            ProvenFactKind::Postcondition,
            "result == old(x) + 1",
            None,
            "add_one_ensures",
        );
        assert_eq!(fact.kind(), ProvenFactKind::Postcondition);
        assert_eq!(fact.expression(), "result == old(x) + 1");
        assert!(fact.source_location().is_none());
    }

    // -- Serialization round-trip tests --

    #[test]
    fn test_proven_fact_kind_serde_round_trip() {
        let kinds = [
            ProvenFactKind::Assertion,
            ProvenFactKind::Precondition,
            ProvenFactKind::Postcondition,
            ProvenFactKind::Invariant,
        ];
        for kind in &kinds {
            let json = serde_json::to_string(kind).expect("serialize kind");
            let back: ProvenFactKind = serde_json::from_str(&json).expect("deserialize kind");
            assert_eq!(*kind, back);
        }
    }

    #[test]
    fn test_proven_fact_serde_round_trip_with_location() {
        let fact = ProvenFact::new(
            ProvenFactKind::Invariant,
            "i < n",
            Some("src/loop.rs:10:9".to_string()),
            "loop_bound",
        );
        let json = serde_json::to_string(&fact).expect("serialize fact");
        let back: ProvenFact = serde_json::from_str(&json).expect("deserialize fact");
        assert_eq!(fact, back);
    }

    #[test]
    fn test_proven_fact_serde_round_trip_without_location() {
        let fact = ProvenFact::new(ProvenFactKind::Assertion, "a != 0", None, "div_guard");
        let json = serde_json::to_string(&fact).expect("serialize fact");
        let back: ProvenFact = serde_json::from_str(&json).expect("deserialize fact");
        assert_eq!(fact, back);
    }

    // -- phase_to_fact_kind tests --

    #[test]
    fn test_phase_to_fact_kind_assertion() {
        assert_eq!(
            phase_to_fact_kind(VerificationPhase::Assertion),
            Some(ProvenFactKind::Assertion)
        );
    }

    #[test]
    fn test_phase_to_fact_kind_assert_by() {
        assert_eq!(
            phase_to_fact_kind(VerificationPhase::AssertBy),
            Some(ProvenFactKind::Assertion)
        );
    }

    #[test]
    fn test_phase_to_fact_kind_recommendation() {
        assert_eq!(
            phase_to_fact_kind(VerificationPhase::Recommendation),
            Some(ProvenFactKind::Precondition)
        );
    }

    #[test]
    fn test_phase_to_fact_kind_loop_ensures() {
        assert_eq!(
            phase_to_fact_kind(VerificationPhase::LoopEnsures),
            Some(ProvenFactKind::Postcondition)
        );
    }

    #[test]
    fn test_phase_to_fact_kind_loop_invariant() {
        assert_eq!(
            phase_to_fact_kind(VerificationPhase::LoopInvariant),
            Some(ProvenFactKind::Invariant)
        );
    }

    #[test]
    fn test_phase_to_fact_kind_loop_invariant_inductive_step() {
        assert_eq!(
            phase_to_fact_kind(VerificationPhase::LoopInvariantInductiveStep),
            Some(ProvenFactKind::Invariant)
        );
    }

    #[test]
    fn test_phase_to_fact_kind_vacuous_precheck_returns_none() {
        assert_eq!(phase_to_fact_kind(VerificationPhase::VacuousPrecheck), None);
    }

    #[test]
    fn test_phase_to_fact_kind_parallel_proof_returns_none() {
        assert_eq!(phase_to_fact_kind(VerificationPhase::ParallelProof), None);
    }

    // -- extract_proven_facts integration tests --

    #[test]
    fn test_extract_proven_facts_empty_report() {
        let report = make_report(vec![]);
        let facts = extract_proven_facts(&report);
        assert!(facts.is_empty());
    }

    #[test]
    fn test_extract_proven_facts_all_verified() {
        let report = make_report(vec![
            make_step(
                VerificationPhase::Assertion,
                "x > 0",
                Some("src/lib.rs:10:5"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::LoopInvariant,
                "i < n",
                Some("src/lib.rs:20:9"),
                StepResultKind::Verified,
            ),
        ]);

        let facts = extract_proven_facts(&report);
        assert_eq!(facts.len(), 2);
        assert_eq!(facts[0].kind(), ProvenFactKind::Assertion);
        assert_eq!(facts[0].expression(), "x > 0");
        assert_eq!(facts[0].source_location(), Some("src/lib.rs:10:5"));
        assert_eq!(facts[1].kind(), ProvenFactKind::Invariant);
        assert_eq!(facts[1].expression(), "i < n");
    }

    #[test]
    fn test_extract_proven_facts_filters_non_verified_steps() {
        let report = make_report(vec![
            make_step(
                VerificationPhase::Assertion,
                "guard_ok",
                Some("src/a.rs:1:1"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::Assertion,
                "fails_here",
                Some("src/a.rs:5:1"),
                StepResultKind::Counterexample,
            ),
            make_step(
                VerificationPhase::LoopInvariant,
                "timeout_inv",
                None,
                StepResultKind::Unknown,
            ),
            make_step(
                VerificationPhase::AssertBy,
                "error_step",
                None,
                StepResultKind::Error,
            ),
        ]);

        let facts = extract_proven_facts(&report);
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].expression(), "guard_ok");
    }

    #[test]
    fn test_extract_proven_facts_skips_vacuous_precheck() {
        let report = make_report(vec![
            make_step(
                VerificationPhase::VacuousPrecheck,
                "vacuity_check",
                None,
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::Assertion,
                "real_assertion",
                Some("src/a.rs:1:1"),
                StepResultKind::Verified,
            ),
        ]);

        let facts = extract_proven_facts(&report);
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].expression(), "real_assertion");
    }

    #[test]
    fn test_extract_proven_facts_skips_parallel_proof() {
        let report = make_report(vec![make_step(
            VerificationPhase::ParallelProof,
            "parallel_step",
            None,
            StepResultKind::Verified,
        )]);

        let facts = extract_proven_facts(&report);
        assert!(facts.is_empty());
    }

    #[test]
    fn test_extract_proven_facts_mixed_phases() {
        let report = make_report(vec![
            make_step(
                VerificationPhase::Recommendation,
                "requires x > 0",
                Some("src/f.rs:3:1"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::LoopEnsures,
                "result == sum",
                Some("src/f.rs:15:1"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::LoopInvariantInductiveStep,
                "acc >= 0",
                Some("src/f.rs:10:9"),
                StepResultKind::Verified,
            ),
        ]);

        let facts = extract_proven_facts(&report);
        assert_eq!(facts.len(), 3);
        assert_eq!(facts[0].kind(), ProvenFactKind::Precondition);
        assert_eq!(facts[1].kind(), ProvenFactKind::Postcondition);
        assert_eq!(facts[2].kind(), ProvenFactKind::Invariant);
    }

    #[test]
    fn test_extract_proven_facts_preserves_source_location_none() {
        let report = make_report(vec![make_step(
            VerificationPhase::Assertion,
            "no_location",
            None,
            StepResultKind::Verified,
        )]);

        let facts = extract_proven_facts(&report);
        assert_eq!(facts.len(), 1);
        assert!(facts[0].source_location().is_none());
    }

    #[test]
    fn test_extract_proven_facts_skipped_steps_excluded() {
        let report = make_report(vec![
            make_step(
                VerificationPhase::Assertion,
                "verified_one",
                Some("src/a.rs:1:1"),
                StepResultKind::Verified,
            ),
            // Skipped steps are filtered because result != Verified
            make_step(
                VerificationPhase::Assertion,
                "skipped_one",
                Some("src/a.rs:5:1"),
                StepResultKind::Skipped,
            ),
        ]);

        let facts = extract_proven_facts(&report);
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].expression(), "verified_one");
    }
}
