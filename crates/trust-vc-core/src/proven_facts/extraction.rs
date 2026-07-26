// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Structured extraction of proven facts from [`VerificationReport`].
//!
//! While [`super::extract_proven_facts`] returns only verified steps,
//! this module provides [`ProvenFacts`] — a complete, serializable
//! snapshot of every assertion outcome in a verification report. Each
//! [`AssertionFact`] carries the function name, assertion name, source
//! location, proof status, and the original expression text.
//!
//! Downstream consumers (the optimization pipeline in `cargo-trust-vc`,
//! proof certificates, IDE integrations) use [`ProvenFacts`] as the
//! bridge between raw `VerificationReport` data and structured
//! optimization decisions.

use serde::{Deserialize, Serialize};

use crate::verification_report::{StepResultKind, VerificationPhase, VerificationReport};

use super::ProvenFactKind;

// ---------------------------------------------------------------------------
// ProofStatus
// ---------------------------------------------------------------------------

/// Proof status of a single assertion or obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ProofStatus {
    /// The solver proved the assertion holds for all inputs.
    Verified,
    /// The solver found a counterexample — the assertion does not hold.
    Failed,
    /// The solver could not determine the result (e.g., timeout).
    Unknown,
    /// An internal error prevented verification.
    Error,
    /// The step was skipped (e.g., vacuous precheck, parallel proof).
    Skipped,
}

impl std::fmt::Display for ProofStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
            Self::Unknown => "unknown",
            Self::Error => "error",
            Self::Skipped => "skipped",
        };
        write!(f, "{label}")
    }
}

impl From<StepResultKind> for ProofStatus {
    fn from(kind: StepResultKind) -> Self {
        match kind {
            StepResultKind::Verified => Self::Verified,
            // Both are verdicts of failure. `ProofStatus::Failed` carries no
            // model, so the model-less non-proof maps onto it exactly.
            StepResultKind::Counterexample | StepResultKind::NotProved => Self::Failed,
            StepResultKind::Unknown => Self::Unknown,
            StepResultKind::Error => Self::Error,
            StepResultKind::Skipped => Self::Skipped,
        }
    }
}

// ---------------------------------------------------------------------------
// AssertionFact
// ---------------------------------------------------------------------------

/// A single assertion or obligation extracted from a verification report,
/// carrying its proof status.
///
/// Unlike [`super::ProvenFact`] (which only represents verified facts),
/// an `AssertionFact` records every step outcome — verified, failed,
/// unknown, error, or skipped — so downstream consumers can make
/// decisions about both proven and unproven paths.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub struct AssertionFact {
    /// The function that contains this assertion.
    function_name: String,
    /// The assertion or obligation name (step label from the report).
    assertion_name: String,
    /// The expression text from the verification condition.
    condition: String,
    /// Source location if available (e.g., `"src/lib.rs:42:5"`).
    source_location: Option<String>,
    /// What kind of proof obligation produced this fact.
    kind: ProvenFactKind,
    /// The proof outcome.
    status: ProofStatus,
    /// Wall-clock time spent on this step, in milliseconds.
    elapsed_ms: u64,
}

impl AssertionFact {
    /// Creates a new assertion fact.
    #[must_use]
    pub fn new(
        function_name: impl Into<String>,
        assertion_name: impl Into<String>,
        condition: impl Into<String>,
        source_location: Option<String>,
        kind: ProvenFactKind,
        status: ProofStatus,
        elapsed_ms: u64,
    ) -> Self {
        Self {
            function_name: function_name.into(),
            assertion_name: assertion_name.into(),
            condition: condition.into(),
            source_location,
            kind,
            status,
            elapsed_ms,
        }
    }

    /// The function containing this assertion.
    #[must_use]
    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    /// The assertion or obligation name.
    #[must_use]
    pub fn assertion_name(&self) -> &str {
        &self.assertion_name
    }

    /// The expression text from the verification condition.
    #[must_use]
    pub fn condition(&self) -> &str {
        &self.condition
    }

    /// Source location, if available.
    #[must_use]
    pub fn source_location(&self) -> Option<&str> {
        self.source_location.as_deref()
    }

    /// What kind of proof obligation this fact represents.
    #[must_use]
    pub const fn kind(&self) -> ProvenFactKind {
        self.kind
    }

    /// The proof outcome.
    #[must_use]
    pub const fn status(&self) -> ProofStatus {
        self.status
    }

    /// Wall-clock time spent on this step, in milliseconds.
    #[must_use]
    pub const fn elapsed_ms(&self) -> u64 {
        self.elapsed_ms
    }

    /// Returns `true` if this fact was proven (status is `Verified`).
    #[must_use]
    pub const fn is_verified(&self) -> bool {
        matches!(self.status, ProofStatus::Verified)
    }
}

// ---------------------------------------------------------------------------
// ProvenFacts
// ---------------------------------------------------------------------------

/// Aggregated extraction of assertion facts from one or more verification
/// reports.
///
/// This is the primary interface for the compilation optimization pipeline:
/// it collects every assertion outcome (verified, failed, unknown) so that
/// downstream consumers can emit `unreachable_unchecked()` for proven
/// assertions, generate warnings for failed ones, and report coverage for
/// unknown ones.
///
/// # Construction
///
/// Use [`ProvenFacts::from_report`] for a single function or
/// [`ProvenFacts::from_reports`] for a batch of `(function_name, report)`
/// pairs.
///
/// # Examples
///
/// ```no_run
/// use trust_vc_core::proven_facts::extraction::ProvenFacts;
/// use trust_vc_core::VerificationReport;
///
/// fn process(name: &str, report: &VerificationReport) {
///     let facts = ProvenFacts::from_report(name, report);
///     println!("verified: {}, total: {}", facts.verified_count(), facts.total_count());
///     for fact in facts.verified() {
///         println!("  proven: {} at {:?}", fact.condition(), fact.source_location());
///     }
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ProvenFacts {
    /// All extracted assertion facts, in report order.
    facts: Vec<AssertionFact>,
}

impl ProvenFacts {
    /// Extract all assertion facts from a single verification report.
    ///
    /// `function_name` is attached to every extracted fact so that
    /// downstream consumers can group and filter by function.
    #[must_use]
    pub fn from_report(function_name: &str, report: &VerificationReport) -> Self {
        let facts = report
            .steps()
            .iter()
            .filter_map(|step| {
                let kind = phase_to_fact_kind(step.phase())?;
                Some(AssertionFact {
                    function_name: function_name.to_string(),
                    assertion_name: step.label().to_string(),
                    condition: step.label().to_string(),
                    source_location: step.location().map(str::to_string),
                    kind,
                    status: ProofStatus::from(step.result()),
                    elapsed_ms: u64::try_from(step.elapsed().as_millis()).unwrap_or(u64::MAX),
                })
            })
            .collect();

        Self { facts }
    }

    /// Extract assertion facts from multiple `(function_name, report)` pairs.
    #[must_use]
    pub fn from_reports<'a>(
        reports: impl IntoIterator<Item = (&'a str, &'a VerificationReport)>,
    ) -> Self {
        let mut facts = Vec::new();
        for (name, report) in reports {
            let single = Self::from_report(name, report);
            facts.extend(single.facts);
        }
        Self { facts }
    }

    /// All extracted assertion facts, in report order.
    #[must_use]
    pub fn facts(&self) -> &[AssertionFact] {
        &self.facts
    }

    /// Total number of extracted assertion facts.
    #[must_use]
    pub fn total_count(&self) -> usize {
        self.facts.len()
    }

    /// Number of verified (proven) assertions.
    #[must_use]
    pub fn verified_count(&self) -> usize {
        self.facts
            .iter()
            .filter(|f| f.status == ProofStatus::Verified)
            .count()
    }

    /// Number of failed assertions (counterexamples found).
    #[must_use]
    pub fn failed_count(&self) -> usize {
        self.facts
            .iter()
            .filter(|f| f.status == ProofStatus::Failed)
            .count()
    }

    /// Number of unknown-status assertions.
    #[must_use]
    pub fn unknown_count(&self) -> usize {
        self.facts
            .iter()
            .filter(|f| f.status == ProofStatus::Unknown)
            .count()
    }

    /// Iterator over only the verified (proven) facts.
    pub fn verified(&self) -> impl Iterator<Item = &AssertionFact> {
        self.facts
            .iter()
            .filter(|f| f.status == ProofStatus::Verified)
    }

    /// Iterator over only the failed facts.
    pub fn failed(&self) -> impl Iterator<Item = &AssertionFact> {
        self.facts
            .iter()
            .filter(|f| f.status == ProofStatus::Failed)
    }

    /// Iterator over only the unknown-status facts.
    pub fn unknown(&self) -> impl Iterator<Item = &AssertionFact> {
        self.facts
            .iter()
            .filter(|f| f.status == ProofStatus::Unknown)
    }

    /// Distinct function names present in the extracted facts.
    #[must_use]
    pub fn function_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self
            .facts
            .iter()
            .map(|f| f.function_name.as_str())
            .collect();
        names.sort_unstable();
        names.dedup();
        names
    }

    /// Facts for a specific function.
    pub fn facts_for_function<'a>(
        &'a self,
        function_name: &'a str,
    ) -> impl Iterator<Item = &'a AssertionFact> {
        self.facts
            .iter()
            .filter(move |f| f.function_name == function_name)
    }

    /// Returns `true` if every extracted assertion was verified.
    #[must_use]
    pub fn all_verified(&self) -> bool {
        self.facts
            .iter()
            .all(|f| f.status == ProofStatus::Verified || f.status == ProofStatus::Skipped)
    }

    /// Merge another `ProvenFacts` into this one.
    pub fn merge(&mut self, other: Self) {
        self.facts.extend(other.facts);
    }
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Maps a `VerificationPhase` to a `ProvenFactKind`.
///
/// Returns `None` for phases that do not directly map to a user-facing
/// proof obligation (e.g., `VacuousPrecheck`, `ParallelProof`).
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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

    // -- ProofStatus tests --

    #[test]
    fn test_proof_status_display() {
        assert_eq!(ProofStatus::Verified.to_string(), "verified");
        assert_eq!(ProofStatus::Failed.to_string(), "failed");
        assert_eq!(ProofStatus::Unknown.to_string(), "unknown");
        assert_eq!(ProofStatus::Error.to_string(), "error");
        assert_eq!(ProofStatus::Skipped.to_string(), "skipped");
    }

    #[test]
    fn test_proof_status_from_step_result_kind() {
        assert_eq!(
            ProofStatus::from(StepResultKind::Verified),
            ProofStatus::Verified
        );
        assert_eq!(
            ProofStatus::from(StepResultKind::Counterexample),
            ProofStatus::Failed
        );
        assert_eq!(
            ProofStatus::from(StepResultKind::Unknown),
            ProofStatus::Unknown
        );
        assert_eq!(ProofStatus::from(StepResultKind::Error), ProofStatus::Error);
        assert_eq!(
            ProofStatus::from(StepResultKind::Skipped),
            ProofStatus::Skipped
        );
    }

    #[test]
    fn test_proof_status_serde_round_trip() {
        let statuses = [
            ProofStatus::Verified,
            ProofStatus::Failed,
            ProofStatus::Unknown,
            ProofStatus::Error,
            ProofStatus::Skipped,
        ];
        for status in &statuses {
            let json = serde_json::to_string(status).expect("serialize");
            let back: ProofStatus = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(*status, back);
        }
    }

    // -- AssertionFact tests --

    #[test]
    fn test_assertion_fact_new_and_accessors() {
        let fact = AssertionFact::new(
            "my_function",
            "nonneg_check",
            "x > 0",
            Some("src/lib.rs:42:5".to_string()),
            ProvenFactKind::Assertion,
            ProofStatus::Verified,
            12,
        );
        assert_eq!(fact.function_name(), "my_function");
        assert_eq!(fact.assertion_name(), "nonneg_check");
        assert_eq!(fact.condition(), "x > 0");
        assert_eq!(fact.source_location(), Some("src/lib.rs:42:5"));
        assert_eq!(fact.kind(), ProvenFactKind::Assertion);
        assert_eq!(fact.status(), ProofStatus::Verified);
        assert_eq!(fact.elapsed_ms(), 12);
        assert!(fact.is_verified());
    }

    #[test]
    fn test_assertion_fact_is_verified_false_for_failed() {
        let fact = AssertionFact::new(
            "f",
            "check",
            "x > 0",
            None,
            ProvenFactKind::Assertion,
            ProofStatus::Failed,
            5,
        );
        assert!(!fact.is_verified());
    }

    #[test]
    fn test_assertion_fact_serde_round_trip() {
        let fact = AssertionFact::new(
            "my_fn",
            "bound_check",
            "i < arr.len()",
            Some("src/loop.rs:10:5".to_string()),
            ProvenFactKind::Invariant,
            ProofStatus::Verified,
            7,
        );
        let json = serde_json::to_string(&fact).expect("serialize");
        let back: AssertionFact = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(fact, back);
    }

    // -- ProvenFacts::from_report tests --

    #[test]
    fn test_from_report_empty() {
        let report = make_report(vec![]);
        let facts = ProvenFacts::from_report("empty_fn", &report);
        assert_eq!(facts.total_count(), 0);
        assert_eq!(facts.verified_count(), 0);
        assert!(facts.all_verified());
    }

    #[test]
    fn test_from_report_all_verified() {
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

        let facts = ProvenFacts::from_report("test_fn", &report);
        assert_eq!(facts.total_count(), 2);
        assert_eq!(facts.verified_count(), 2);
        assert_eq!(facts.failed_count(), 0);
        assert_eq!(facts.unknown_count(), 0);
        assert!(facts.all_verified());

        let verified: Vec<_> = facts.verified().collect();
        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].function_name(), "test_fn");
        assert_eq!(verified[0].condition(), "x > 0");
        assert_eq!(verified[0].kind(), ProvenFactKind::Assertion);
        assert_eq!(verified[1].condition(), "i < n");
        assert_eq!(verified[1].kind(), ProvenFactKind::Invariant);
    }

    #[test]
    fn test_from_report_mixed_results() {
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

        let facts = ProvenFacts::from_report("mixed_fn", &report);
        assert_eq!(facts.total_count(), 4);
        assert_eq!(facts.verified_count(), 1);
        assert_eq!(facts.failed_count(), 1);
        assert_eq!(facts.unknown_count(), 1);
        assert!(!facts.all_verified());

        let failed: Vec<_> = facts.failed().collect();
        assert_eq!(failed.len(), 1);
        assert_eq!(failed[0].assertion_name(), "fails_here");
        assert_eq!(failed[0].status(), ProofStatus::Failed);

        let unknown: Vec<_> = facts.unknown().collect();
        assert_eq!(unknown.len(), 1);
        assert_eq!(unknown[0].assertion_name(), "timeout_inv");
    }

    #[test]
    fn test_from_report_skips_vacuous_precheck() {
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

        let facts = ProvenFacts::from_report("fn_with_precheck", &report);
        assert_eq!(facts.total_count(), 1);
        assert_eq!(facts.facts()[0].assertion_name(), "real_assertion");
    }

    #[test]
    fn test_from_report_skips_parallel_proof() {
        let report = make_report(vec![make_step(
            VerificationPhase::ParallelProof,
            "parallel_step",
            None,
            StepResultKind::Verified,
        )]);

        let facts = ProvenFacts::from_report("fn_parallel", &report);
        assert_eq!(facts.total_count(), 0);
    }

    #[test]
    fn test_from_report_preserves_location_none() {
        let report = make_report(vec![make_step(
            VerificationPhase::Assertion,
            "no_location",
            None,
            StepResultKind::Verified,
        )]);

        let facts = ProvenFacts::from_report("fn_noloc", &report);
        assert_eq!(facts.total_count(), 1);
        assert!(facts.facts()[0].source_location().is_none());
    }

    #[test]
    fn test_from_report_maps_phases_correctly() {
        let report = make_report(vec![
            make_step(
                VerificationPhase::Recommendation,
                "requires x > 0",
                Some("f.rs:3:1"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::LoopEnsures,
                "result == sum",
                Some("f.rs:15:1"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::LoopInvariantInductiveStep,
                "acc >= 0",
                Some("f.rs:10:9"),
                StepResultKind::Verified,
            ),
        ]);

        let facts = ProvenFacts::from_report("fn_phases", &report);
        assert_eq!(facts.total_count(), 3);
        assert_eq!(facts.facts()[0].kind(), ProvenFactKind::Precondition);
        assert_eq!(facts.facts()[1].kind(), ProvenFactKind::Postcondition);
        assert_eq!(facts.facts()[2].kind(), ProvenFactKind::Invariant);
    }

    // -- ProvenFacts::from_reports tests --

    #[test]
    fn test_from_reports_multiple_functions() {
        let report_a = make_report(vec![make_step(
            VerificationPhase::Assertion,
            "a_ok",
            Some("a.rs:1:1"),
            StepResultKind::Verified,
        )]);
        let report_b = make_report(vec![
            make_step(
                VerificationPhase::Assertion,
                "b_ok",
                Some("b.rs:1:1"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::LoopInvariant,
                "b_inv",
                Some("b.rs:5:1"),
                StepResultKind::Counterexample,
            ),
        ]);

        let facts = ProvenFacts::from_reports([("fn_a", &report_a), ("fn_b", &report_b)]);
        assert_eq!(facts.total_count(), 3);
        assert_eq!(facts.verified_count(), 2);
        assert_eq!(facts.failed_count(), 1);

        let mut names = facts.function_names();
        names.sort();
        assert_eq!(names, vec!["fn_a", "fn_b"]);
    }

    #[test]
    fn test_facts_for_function_filters_correctly() {
        let report_a = make_report(vec![make_step(
            VerificationPhase::Assertion,
            "a_check",
            None,
            StepResultKind::Verified,
        )]);
        let report_b = make_report(vec![make_step(
            VerificationPhase::Assertion,
            "b_check",
            None,
            StepResultKind::Counterexample,
        )]);

        let facts = ProvenFacts::from_reports([("fn_a", &report_a), ("fn_b", &report_b)]);

        let a_facts: Vec<_> = facts.facts_for_function("fn_a").collect();
        assert_eq!(a_facts.len(), 1);
        assert_eq!(a_facts[0].assertion_name(), "a_check");

        let b_facts: Vec<_> = facts.facts_for_function("fn_b").collect();
        assert_eq!(b_facts.len(), 1);
        assert_eq!(b_facts[0].assertion_name(), "b_check");

        let c_facts: Vec<_> = facts.facts_for_function("fn_c").collect();
        assert!(c_facts.is_empty());
    }

    // -- ProvenFacts::merge tests --

    #[test]
    fn test_merge_combines_facts() {
        let report_a = make_report(vec![make_step(
            VerificationPhase::Assertion,
            "a_ok",
            None,
            StepResultKind::Verified,
        )]);
        let report_b = make_report(vec![make_step(
            VerificationPhase::Assertion,
            "b_ok",
            None,
            StepResultKind::Verified,
        )]);

        let mut facts_a = ProvenFacts::from_report("fn_a", &report_a);
        let facts_b = ProvenFacts::from_report("fn_b", &report_b);
        assert_eq!(facts_a.total_count(), 1);

        facts_a.merge(facts_b);
        assert_eq!(facts_a.total_count(), 2);
        assert_eq!(facts_a.function_names().len(), 2);
    }

    // -- all_verified edge cases --

    #[test]
    fn test_all_verified_with_skipped_steps_returns_true() {
        let report = make_report(vec![
            make_step(
                VerificationPhase::Assertion,
                "ok",
                None,
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::Assertion,
                "skip",
                None,
                StepResultKind::Skipped,
            ),
        ]);
        let facts = ProvenFacts::from_report("fn", &report);
        assert!(facts.all_verified());
    }

    // -- Serde round-trip --

    #[test]
    fn test_proven_facts_serde_round_trip() {
        let report = make_report(vec![
            make_step(
                VerificationPhase::Assertion,
                "x > 0",
                Some("src/lib.rs:42:5"),
                StepResultKind::Verified,
            ),
            make_step(
                VerificationPhase::LoopInvariant,
                "i < n",
                None,
                StepResultKind::Counterexample,
            ),
        ]);
        let facts = ProvenFacts::from_report("test_fn", &report);
        let json = serde_json::to_string_pretty(&facts).expect("serialize");
        let back: ProvenFacts = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(facts, back);
    }

    #[test]
    fn test_proven_facts_json_structure() {
        let report = make_report(vec![make_step(
            VerificationPhase::Assertion,
            "guard",
            Some("src/lib.rs:10:5"),
            StepResultKind::Verified,
        )]);
        let facts = ProvenFacts::from_report("my_fn", &report);
        let json = serde_json::to_string(&facts).expect("serialize");
        let parsed: serde_json::Value = serde_json::from_str(&json).expect("must be valid JSON");
        assert!(parsed["facts"].is_array());
        let arr = parsed["facts"].as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["function_name"], "my_fn");
        assert_eq!(arr[0]["assertion_name"], "guard");
        assert_eq!(arr[0]["status"], "Verified");
        assert_eq!(arr[0]["kind"], "Assertion");
    }
}
