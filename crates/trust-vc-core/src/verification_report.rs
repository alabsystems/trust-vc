//! Sidecar verification diagnostics reporting.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#[cfg(test)]
use std::collections::BTreeMap;
use std::time::Duration;

use ay_dpll::api::SolveDetails;
#[cfg(feature = "proof-certificates")]
use ay_dpll::api::{StrictProofVerdict, UnsatProofArtifact};

use crate::encoder::AssertionOutcome;
use crate::prepared_context::PreparedObligation;
use crate::verification_bridge::PipelineDiagnostic;
use crate::UnknownCategory;
use crate::VerifyResult;

mod capture;
#[cfg(feature = "proof-certificates")]
pub(crate) mod kernel_bridge;
mod render;
mod solver_stats;

pub use solver_stats::{SolverStatValue, SolverStats};

pub(crate) use capture::{
    begin_obligation_step, begin_step, capture_report, end_step_skipped, end_step_verified,
    end_step_with_assertion_result, end_step_with_verify_result, record_demand_inline_recovery,
    record_solve_details, record_used_assumptions, step_from_verify_result,
    with_capture_suppressed,
};
#[cfg(feature = "proof-certificates")]
pub(crate) use capture::{current_proof_is_strict, record_proof_artifact};
pub(crate) use render::emit_verbose_report_if_enabled;

/// Formatting and capture options for sidecar verification reports.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[must_use]
pub struct VerificationReportOptions {
    verbose: bool,
}

impl VerificationReportOptions {
    /// Construct default report options.
    pub const fn new() -> Self {
        Self { verbose: false }
    }

    /// Whether verbose rendering is enabled.
    #[must_use]
    pub const fn verbose(self) -> bool {
        self.verbose
    }

    /// Return a copy with the `verbose` flag changed.
    pub const fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Read `TRUST_VC_VERBOSE` from the environment.
    pub fn from_env() -> Self {
        let verbose = std::env::var("TRUST_VC_VERBOSE")
            .ok()
            .map(|raw| raw.trim().to_ascii_lowercase())
            .is_some_and(|raw| matches!(raw.as_str(), "1" | "true" | "yes" | "on"));
        Self { verbose }
    }
}

/// Pre-flight pipeline summary copied into a report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[must_use]
pub struct PipelineSummary {
    num_obligations: usize,
    num_variables: usize,
    has_assertions: bool,
    has_assumptions: bool,
}

impl PipelineSummary {
    #[must_use]
    pub const fn num_obligations(self) -> usize {
        self.num_obligations
    }

    #[must_use]
    pub const fn num_variables(self) -> usize {
        self.num_variables
    }

    #[must_use]
    pub const fn has_assertions(self) -> bool {
        self.has_assertions
    }

    #[must_use]
    pub const fn has_assumptions(self) -> bool {
        self.has_assumptions
    }
}

impl From<&PipelineDiagnostic> for PipelineSummary {
    fn from(value: &PipelineDiagnostic) -> Self {
        Self {
            num_obligations: value.num_obligations(),
            num_variables: value.num_variables(),
            has_assertions: value.has_assertions(),
            has_assumptions: value.has_assumptions(),
        }
    }
}

/// Verification step category.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VerificationPhase {
    Assertion,
    LoopInvariant,
    LoopInvariantInductiveStep,
    /// Loop termination measure (`loop_decreases!`) obligation: the WF1
    /// non-negativity floor (a direct single-state entailment under the loop
    /// invariants + guard) and the WF2 strict-descent step (a frame-condition
    /// inductive step). Neither is a reusable proven fact (a decrease
    /// `measure < entry` is not an invariant, and the floor is measure-scoped),
    /// so `phase_to_fact_kind` maps it to `None` via its `_` fallback.
    LoopDecreases,
    LoopEnsures,
    AssertBy,
    Recommendation,
    ParallelProof,
    VacuousPrecheck,
}

impl std::fmt::Display for VerificationPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::Assertion => "assertion",
            Self::LoopInvariant => "loop invariant",
            Self::LoopInvariantInductiveStep => "loop invariant inductive step",
            Self::LoopDecreases => "loop decreases",
            Self::LoopEnsures => "loop ensures",
            Self::AssertBy => "assert_by",
            Self::Recommendation => "recommends",
            Self::ParallelProof => "parallel proof",
            Self::VacuousPrecheck => "vacuous precheck",
        };
        write!(f, "{label}")
    }
}

/// Public result kind for one verification step.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum StepResultKind {
    Verified,
    Counterexample,
    /// The obligation was not discharged because of a genuine theory
    /// incompleteness, with **no model**. The report-layer mirror of
    /// [`crate::VerifyResult::NotProved`]; kept distinct from `Counterexample`
    /// so a report never narrates a counterexample that was never found, and
    /// from `Unknown` so a failure is never rendered as merely inconclusive.
    NotProved,
    Unknown,
    Error,
    Skipped,
}

impl std::fmt::Display for StepResultKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let label = match self {
            Self::Verified => "verified",
            Self::Counterexample => "counterexample",
            Self::NotProved => "not-proved",
            Self::Unknown => "unknown",
            Self::Error => "error",
            Self::Skipped => "skipped",
        };
        write!(f, "{label}")
    }
}

/// Unknown-category diagnostics plus an actionable suggestion.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct UnknownDiagnostic {
    category: UnknownCategory,
    suggestion: &'static str,
}

impl UnknownDiagnostic {
    #[must_use]
    pub const fn category(&self) -> UnknownCategory {
        self.category
    }

    #[must_use]
    pub const fn suggestion(&self) -> &'static str {
        self.suggestion
    }
}

/// Recovery metadata for assertions that only verified after retry-local
/// demand-driven body inlining.
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct DemandInlineRecovery {
    inlined_functions: Vec<String>,
    depth_used: usize,
}

impl DemandInlineRecovery {
    #[must_use]
    pub fn inlined_functions(&self) -> &[String] {
        &self.inlined_functions
    }

    #[must_use]
    pub const fn depth_used(&self) -> usize {
        self.depth_used
    }
}

/// TrustVc-owned UNSAT proof certificate extracted from ay-dpll.
///
/// Available only when the `proof-certificates` feature is enabled and the
/// solver produces a proof for a verified result.
#[cfg(feature = "proof-certificates")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct ProofCertificate {
    alethe: String,
    strict_verified: bool,
    clean_supported: bool,
    trust_count: u32,
    hole_count: u32,
    resolution_count: u32,
    theory_count: u32,
    kernel_verified: bool,
}

#[cfg(feature = "proof-certificates")]
impl ProofCertificate {
    /// Rendered Alethe proof text (SMT-LIB compatible).
    #[must_use]
    pub fn alethe(&self) -> &str {
        &self.alethe
    }

    /// Whether the strict proof checker accepted this proof.
    #[must_use]
    pub const fn strict_verified(&self) -> bool {
        self.strict_verified
    }

    /// Whether the proof uses only clean-supported rules.
    #[must_use]
    pub const fn clean_supported(&self) -> bool {
        self.clean_supported
    }

    /// Number of trust steps (unverified axioms).
    #[must_use]
    pub const fn trust_count(&self) -> u32 {
        self.trust_count
    }

    /// Number of hole steps (gaps in the proof).
    #[must_use]
    pub const fn hole_count(&self) -> u32 {
        self.hole_count
    }

    /// Number of resolution steps.
    #[must_use]
    pub const fn resolution_count(&self) -> u32 {
        self.resolution_count
    }

    /// Number of theory lemma steps.
    #[must_use]
    pub const fn theory_count(&self) -> u32 {
        self.theory_count
    }

    /// Whether the trust-vc-kernel independent checker verified this proof.
    #[must_use]
    pub const fn kernel_verified(&self) -> bool {
        self.kernel_verified
    }

    /// Return a copy with the `kernel_verified` flag changed.
    pub(crate) fn with_kernel_verified(mut self, verified: bool) -> Self {
        self.kernel_verified = verified;
        self
    }

    pub(crate) fn from_artifact(artifact: &UnsatProofArtifact) -> Self {
        Self {
            alethe: artifact.alethe.clone(),
            strict_verified: matches!(artifact.strict_verdict, StrictProofVerdict::Verified(_)),
            clean_supported: artifact.clean_supported,
            trust_count: artifact.quality.trust_count,
            hole_count: artifact.quality.hole_count,
            resolution_count: artifact.quality.resolution_count,
            theory_count: artifact.quality.theory_lemma_count,
            kernel_verified: false,
        }
    }
}

/// One executed verification step.
#[derive(Debug, Clone, PartialEq)]
#[must_use]
pub struct StepDiagnostic {
    label: String,
    condition: Option<String>,
    location: Option<String>,
    phase: VerificationPhase,
    elapsed: Duration,
    result: StepResultKind,
    unknown: Option<UnknownDiagnostic>,
    solver: Option<SolverStats>,
    demand_inline_recovery: Option<DemandInlineRecovery>,
    used_assumptions: Vec<String>,
    #[cfg(feature = "proof-certificates")]
    proof: Option<ProofCertificate>,
}

impl StepDiagnostic {
    #[must_use]
    pub fn label(&self) -> &str {
        &self.label
    }

    #[must_use]
    pub fn condition(&self) -> Option<&str> {
        self.condition.as_deref()
    }

    #[must_use]
    pub fn location(&self) -> Option<&str> {
        self.location.as_deref()
    }

    #[must_use]
    pub const fn phase(&self) -> VerificationPhase {
        self.phase
    }

    #[must_use]
    pub const fn elapsed(&self) -> Duration {
        self.elapsed
    }

    #[must_use]
    pub const fn result(&self) -> StepResultKind {
        self.result
    }

    #[must_use]
    pub fn unknown(&self) -> Option<&UnknownDiagnostic> {
        self.unknown.as_ref()
    }

    #[must_use]
    pub fn solver(&self) -> Option<&SolverStats> {
        self.solver.as_ref()
    }

    #[must_use]
    pub fn demand_inline_recovery(&self) -> Option<&DemandInlineRecovery> {
        self.demand_inline_recovery.as_ref()
    }

    #[must_use]
    pub fn used_assumptions(&self) -> &[String] {
        &self.used_assumptions
    }

    /// Return the proof certificate captured for this verification step.
    #[cfg(feature = "proof-certificates")]
    #[must_use]
    pub fn proof(&self) -> Option<&ProofCertificate> {
        self.proof.as_ref()
    }

    #[allow(dead_code)] // called from proven_facts scaffolding
    pub(crate) fn pending(
        phase: VerificationPhase,
        label: String,
        location: Option<String>,
    ) -> Self {
        Self::pending_with_condition(phase, label, location, None)
    }

    pub(crate) fn pending_with_condition(
        phase: VerificationPhase,
        label: String,
        location: Option<String>,
        condition: Option<String>,
    ) -> Self {
        Self {
            label,
            condition,
            location,
            phase,
            elapsed: Duration::ZERO,
            result: StepResultKind::Skipped,
            unknown: None,
            solver: None,
            demand_inline_recovery: None,
            used_assumptions: Vec::new(),
            #[cfg(feature = "proof-certificates")]
            proof: None,
        }
    }

    pub(crate) fn from_verify_result(
        phase: VerificationPhase,
        label: String,
        location: Option<String>,
        elapsed: Duration,
        result: &VerifyResult,
    ) -> Self {
        Self::from_verify_result_with_condition(phase, label, location, None, elapsed, result)
    }

    pub(crate) fn from_verify_result_with_condition(
        phase: VerificationPhase,
        label: String,
        location: Option<String>,
        condition: Option<String>,
        elapsed: Duration,
        result: &VerifyResult,
    ) -> Self {
        let mut step = Self::pending_with_condition(phase, label, location, condition);
        step.elapsed = elapsed;
        apply_verify_result(step, result)
    }
}

/// Full sidecar verification report.
#[derive(Debug, Clone, PartialEq)]
#[must_use]
pub struct VerificationReport {
    result: VerifyResult,
    pipeline: Option<PipelineSummary>,
    steps: Vec<StepDiagnostic>,
    total_elapsed: Duration,
    #[cfg(feature = "proof-certificates")]
    proof: Option<ProofCertificate>,
}

impl VerificationReport {
    #[must_use = "verification result should be inspected"]
    pub fn result(&self) -> &VerifyResult {
        &self.result
    }

    #[must_use]
    pub fn pipeline(&self) -> Option<PipelineSummary> {
        self.pipeline
    }

    #[must_use = "step diagnostics should be inspected"]
    pub fn steps(&self) -> &[StepDiagnostic] {
        &self.steps
    }

    #[must_use = "localized step diagnostics should be inspected"]
    pub fn first_non_verified_step(&self) -> Option<&StepDiagnostic> {
        self.steps.iter().find(|step| {
            !matches!(
                step.result(),
                StepResultKind::Verified | StepResultKind::Skipped
            )
        })
    }

    #[must_use]
    pub const fn total_elapsed(&self) -> Duration {
        self.total_elapsed
    }

    /// Returns the UNSAT proof certificate if proof production was enabled
    /// and the result was Verified.
    #[cfg(feature = "proof-certificates")]
    #[must_use]
    pub fn proof(&self) -> Option<&ProofCertificate> {
        self.proof.as_ref()
    }

    pub(crate) fn from_parts(
        result: VerifyResult,
        pipeline: Option<PipelineSummary>,
        steps: Vec<StepDiagnostic>,
        total_elapsed: Duration,
    ) -> Self {
        Self {
            result,
            pipeline,
            steps,
            total_elapsed,
            #[cfg(feature = "proof-certificates")]
            proof: None,
        }
    }

    #[cfg(feature = "proof-certificates")]
    pub(crate) fn with_proof(mut self, proof: Option<ProofCertificate>) -> Self {
        self.proof = proof;
        self
    }
}

fn apply_verify_result(mut step: StepDiagnostic, result: &VerifyResult) -> StepDiagnostic {
    step.result = match result {
        VerifyResult::Verified => StepResultKind::Verified,
        VerifyResult::Counterexample { .. } => StepResultKind::Counterexample,
        VerifyResult::NotProved { .. } => StepResultKind::NotProved,
        VerifyResult::Unknown { .. } => StepResultKind::Unknown,
        VerifyResult::Error { .. } => StepResultKind::Error,
    };
    step.unknown = unknown_from_verify_result(result);
    step
}

fn unknown_from_verify_result(result: &VerifyResult) -> Option<UnknownDiagnostic> {
    result.unknown_category().map(unknown_from_category)
}

fn unknown_from_category(category: UnknownCategory) -> UnknownDiagnostic {
    UnknownDiagnostic {
        category,
        suggestion: category.actionable_suggestion(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn step(label: &str, result: StepResultKind) -> StepDiagnostic {
        StepDiagnostic {
            label: label.to_string(),
            condition: None,
            location: Some("src/lib.rs:10:5".to_string()),
            phase: VerificationPhase::Assertion,
            elapsed: Duration::from_millis(12),
            result,
            unknown: matches!(result, StepResultKind::Unknown).then_some(UnknownDiagnostic {
                category: UnknownCategory::Timeout,
                suggestion: UnknownCategory::Timeout.actionable_suggestion(),
            }),
            solver: None,
            demand_inline_recovery: None,
            used_assumptions: Vec::new(),
            #[cfg(feature = "proof-certificates")]
            proof: None,
        }
    }

    #[test]
    fn test_first_non_verified_step_returns_none_when_all_steps_are_verified() {
        let report = VerificationReport::from_parts(
            VerifyResult::Verified,
            None,
            vec![
                step("precondition", StepResultKind::Verified),
                step("cleanup", StepResultKind::Skipped),
            ],
            Duration::from_millis(20),
        );

        assert!(report.first_non_verified_step().is_none());
    }

    #[test]
    fn test_first_non_verified_step_returns_first_counterexample() {
        let report = VerificationReport::from_parts(
            VerifyResult::Counterexample {
                obligation_name: "postcondition".to_string(),
                model: None,
                bindings: Vec::new(),
            },
            None,
            vec![
                step("precondition", StepResultKind::Verified),
                step("postcondition", StepResultKind::Counterexample),
                step("cleanup", StepResultKind::Error),
            ],
            Duration::from_millis(20),
        );

        let step = report
            .first_non_verified_step()
            .expect("counterexample step should be selected");
        assert_eq!(step.label(), "postcondition");
        assert_eq!(step.result(), StepResultKind::Counterexample);
    }

    #[test]
    fn test_first_non_verified_step_returns_first_unknown_after_verified_steps() {
        let report = VerificationReport::from_parts(
            VerifyResult::unknown(
                "Solver returned unknown (timeout)",
                Some(UnknownCategory::Timeout),
            ),
            None,
            vec![
                step("precondition", StepResultKind::Verified),
                step("calc step 1 of 2", StepResultKind::Skipped),
                step("calc step 2 of 2", StepResultKind::Unknown),
            ],
            Duration::from_millis(20),
        );

        let step = report
            .first_non_verified_step()
            .expect("unknown step should be selected");
        assert_eq!(step.label(), "calc step 2 of 2");
        assert_eq!(step.result(), StepResultKind::Unknown);
        assert_eq!(
            step.unknown().map(|unknown| unknown.category()),
            Some(UnknownCategory::Timeout)
        );
    }
}
