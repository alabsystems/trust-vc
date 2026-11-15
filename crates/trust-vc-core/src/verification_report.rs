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
///
/// # Assertion identity (#2654)
///
/// `refuted_obligation` names the obligation whose NEGATION was asserted into
/// the solver scope that produced this refutation. It is captured at the single
/// recording site (`encoder::verification::solve`) from the very
/// `PreparedObligation` that was just solved, so it is a fact about the query,
/// not a label applied afterwards.
///
/// This exists because certificate-to-obligation binding used to be POSITIONAL
/// (whatever step was on top of the capture stack when the artifact was
/// recorded), and several verification paths issue MORE THAN ONE solver query
/// under a single obligation step — the conjunct split
/// (`verification::split::try_verify_quantified_conjunction_split`) discharges
/// `forall x. (C1 AND C2)` as separate `forall x. Ck` queries. Under positional
/// binding the LAST sub-query's refutation was attached to the parent step, so
/// the parent assertion carried a certificate that refutes only one conjunct.
/// A consumer replaying that Alethe text confirms `Ck`, not the assertion.
/// The identity recorded here lets `capture::record_proof_artifact` refuse that
/// attachment instead of silently over-claiming.
///
/// # Premise binding
///
/// Identity says WHICH query was refuted; it does not say the certificate's
/// `assume` steps ARE that query, and both checkers take the premises as
/// given. A certificate with a premise trust-vc never asserted is a valid
/// refutation of something else. So [`Self::strict_verified`],
/// [`Self::kernel_verified`] and [`Self::clean_supported`] are claims about the
/// OBLIGATION and require [`Self::premises_bound`]; the derivation-only facts
/// are [`Self::derivation_strict_verified`] and
/// [`Self::kernel_skeleton_accepted`]. Binding never changes the verdict: an
/// unbound certificate leaves a `Verified` result standing on the solver.
///
/// A query that AY's term builder folded to `false` binds: the certificate
/// refutes the query trust-vc posed, and what that shows about the obligation
/// rests on the builder's rewrite, as it does for every other certificate.
/// [`Self::query_collapsed`] discloses it. The posed query also holds the
/// no-overflow and collection-precondition predicates trust-vc proved by a
/// separate solve and then assumed; that solve has no certificate, and
/// [`Self::assumed_lemma_premises`] counts the premises that are such
/// predicates.
#[cfg(feature = "proof-certificates")]
#[derive(Debug, Clone, PartialEq, Eq)]
#[must_use]
pub struct ProofCertificate {
    alethe: String,
    /// AY's native strict verdict on the derivation, premises taken as given.
    derivation_strict_verified: bool,
    /// AY's clean-subset verdict on the derivation, premises taken as given.
    derivation_clean_supported: bool,
    trust_count: u32,
    hole_count: u32,
    resolution_count: u32,
    theory_count: u32,
    /// The trust-vc-kernel replayed the refutation (premises taken as given).
    kernel_skeleton_accepted: bool,
    /// Theory lemmas the kernel took as axioms.
    kernel_trusted_theory_lemmas: u32,
    /// Generic rule steps the kernel took as inputs without a check.
    kernel_trusted_rule_steps: u32,
    /// Why the kernel did not accept the proof, when it did not.
    kernel_refusal: Option<String>,
    /// `None` iff every `assume` premise is a term of the query trust-vc posed
    /// for this obligation (or an exact instance of a posed `forall`);
    /// otherwise why not.
    premise_binding_defect: Option<String>,
    /// A premise is the constant `false`: the query collapsed while built.
    query_collapsed: bool,
    /// Premises that are predicates trust-vc proved by a separate,
    /// uncertified solve and then assumed.
    assumed_lemma_premises: u32,
    refuted_obligation: String,
}

#[cfg(feature = "proof-certificates")]
impl ProofCertificate {
    /// Rendered Alethe proof text (SMT-LIB compatible).
    #[must_use]
    pub fn alethe(&self) -> &str {
        &self.alethe
    }

    /// Whether this certificate is strict-checked evidence for its obligation:
    /// AY's strict checker accepted the derivation AND its premises are the
    /// obligation's own query ([`Self::premises_bound`]).
    #[must_use]
    pub const fn strict_verified(&self) -> bool {
        self.derivation_strict_verified && self.premises_bound()
    }

    /// Whether AY's strict checker accepted the derivation, with the premises
    /// taken as given. Not a claim about the obligation; see
    /// [`Self::strict_verified`].
    #[must_use]
    pub const fn derivation_strict_verified(&self) -> bool {
        self.derivation_strict_verified
    }

    /// Whether the proof uses only clean-supported rules and is a refutation of
    /// this obligation's own query ([`Self::premises_bound`]).
    #[must_use]
    pub const fn clean_supported(&self) -> bool {
        self.derivation_clean_supported && self.premises_bound()
    }

    /// Whether every `assume` premise is a term of the query trust-vc posed for
    /// this obligation, or an exact instance of a `forall` it posed.
    #[must_use]
    pub const fn premises_bound(&self) -> bool {
        self.premise_binding_defect.is_none()
    }

    /// Whether a premise is the constant `false`. AY's term builder folded the
    /// query to `false` while trust-vc built it, for example `ret == x * y`
    /// with `ret := x * y`. The refutation is then trivial, and the whole
    /// evidence for the obligation is the builder's rewrite. That rewrite is
    /// trusted, as every builder rewrite is. This withholds no claim; it says
    /// how little the derivation itself carries.
    #[must_use]
    pub const fn query_collapsed(&self) -> bool {
        self.query_collapsed
    }

    /// How many premises are predicates trust-vc proved by a separate solve
    /// and then assumed: the no-overflow and collection-precondition
    /// predicates of the obligation's own arithmetic and indexing. Those
    /// solves record no certificate. With any of them, the certificate shows
    /// the obligation given those predicates, and the predicates rest on the
    /// separate solves' verdicts. This withholds no claim; it says what the
    /// certificate does not cover.
    #[must_use]
    pub const fn assumed_lemma_premises(&self) -> u32 {
        self.assumed_lemma_premises
    }

    /// Why the premises are not this obligation's query, when they are not.
    #[must_use]
    pub fn premise_binding_defect(&self) -> Option<&str> {
        self.premise_binding_defect.as_deref()
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

    /// Whether the trust-vc-kernel independently checked this certificate as a
    /// refutation of its obligation's own query: the premises are bound
    /// ([`Self::premises_bound`]) and the kernel replayed the refutation, every
    /// resolution re-derived with polarity read off the proof's term store and
    /// the empty clause derived by a checked step.
    ///
    /// The kernel has no semantic checker for theory lemmas, and some generic
    /// rule steps are not propositional; it takes those clauses as given. Their
    /// number is [`Self::kernel_trusted_steps`]. Only AY's strict checker
    /// checks them, so when there are any this also requires
    /// [`Self::derivation_strict_verified`]. [`Self::kernel_fully_checked`] is
    /// the claim with none of them.
    #[must_use]
    pub const fn kernel_verified(&self) -> bool {
        self.premises_bound()
            && self.kernel_skeleton_accepted
            && (self.kernel_trusted_steps() == 0 || self.derivation_strict_verified)
    }

    /// Whether the kernel replayed the refutation, with the premises taken as
    /// given. Not a claim about the obligation; see [`Self::kernel_verified`].
    #[must_use]
    pub const fn kernel_skeleton_accepted(&self) -> bool {
        self.kernel_skeleton_accepted
    }

    /// Clauses the kernel took as given: theory lemmas plus generic rule steps
    /// neither it nor the bridge derived.
    #[must_use]
    pub const fn kernel_trusted_steps(&self) -> u32 {
        self.kernel_trusted_theory_lemmas
            .saturating_add(self.kernel_trusted_rule_steps)
    }

    /// Theory lemmas the kernel took as axioms.
    #[must_use]
    pub const fn kernel_trusted_theory_lemmas(&self) -> u32 {
        self.kernel_trusted_theory_lemmas
    }

    /// Generic rule steps the kernel took as inputs without a check.
    #[must_use]
    pub const fn kernel_trusted_rule_steps(&self) -> u32 {
        self.kernel_trusted_rule_steps
    }

    /// [`Self::kernel_verified`] with nothing taken on trust: the kernel and
    /// the bridge derived every clause of the refutation from its premises.
    #[must_use]
    pub const fn kernel_fully_checked(&self) -> bool {
        self.kernel_verified() && self.kernel_trusted_steps() == 0
    }

    /// Why the kernel did not accept the proof, when it did not.
    #[must_use]
    pub fn kernel_refusal(&self) -> Option<&str> {
        self.kernel_refusal.as_deref()
    }

    /// Name of the obligation whose negation the solver actually refuted to
    /// produce this certificate (#2654).
    ///
    /// This is the obligation identity captured at the solve site, NOT the label
    /// of whatever report step happened to be open. A consumer that mints a
    /// per-assertion proof artifact must check this against the assertion it is
    /// certifying; an empty string means the identity was not recorded and the
    /// certificate must not be treated as evidence for any specific assertion.
    #[must_use]
    pub fn refuted_obligation(&self) -> &str {
        &self.refuted_obligation
    }

    /// True iff this certificate is the solver's refutation of `obligation`'s
    /// own negated goal.
    ///
    /// The empty identity never matches, so an unattributed certificate can
    /// never be adopted as evidence for an assertion.
    #[must_use]
    pub fn refutes_obligation(&self, obligation: &str) -> bool {
        !self.refuted_obligation.is_empty() && self.refuted_obligation == obligation
    }

    /// Return a copy carrying what the solve site established about this
    /// certificate: whether its premises are the posed query, and the kernel's
    /// verdict on its derivation.
    pub(crate) fn with_evidence(mut self, evidence: &kernel_bridge::CertificateEvidence) -> Self {
        self.premise_binding_defect = evidence.binding.clone().err();
        self.query_collapsed = evidence.query_collapsed;
        self.assumed_lemma_premises = evidence.assumed_lemma_premises;
        self.kernel_skeleton_accepted = evidence.kernel.skeleton_accepted;
        self.kernel_trusted_theory_lemmas = evidence.kernel.trusted_theory_lemmas;
        self.kernel_trusted_rule_steps = evidence.kernel.trusted_rule_steps;
        self.kernel_refusal = evidence.kernel.refusal.clone();
        self
    }

    /// Mint a certificate from AY's artifact. It starts UNBOUND and
    /// kernel-unchecked, so it makes no claim about its obligation until
    /// [`Self::with_evidence`] records what was established.
    pub(crate) fn from_artifact(artifact: &UnsatProofArtifact, refuted_obligation: &str) -> Self {
        Self {
            alethe: artifact.alethe.clone(),
            derivation_strict_verified: matches!(
                artifact.strict_verdict,
                StrictProofVerdict::Verified(_)
            ),
            derivation_clean_supported: artifact.clean_supported,
            trust_count: artifact.quality.trust_count,
            hole_count: artifact.quality.hole_count,
            resolution_count: artifact.quality.resolution_count,
            theory_count: artifact.quality.theory_lemma_count,
            kernel_skeleton_accepted: false,
            kernel_trusted_theory_lemmas: 0,
            kernel_trusted_rule_steps: 0,
            kernel_refusal: Some("the kernel was not run on this certificate".to_string()),
            premise_binding_defect: Some(
                "the certificate was not checked against its posed query".to_string(),
            ),
            query_collapsed: false,
            assumed_lemma_premises: 0,
            refuted_obligation: refuted_obligation.to_string(),
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

    /// Returns the last UNSAT proof certificate recorded for this report, if
    /// proof production was enabled. It refutes ONE obligation,
    /// [`ProofCertificate::refuted_obligation`], and its claims are about that
    /// obligation only; each step carries the certificate of its own
    /// obligation ([`StepDiagnostic::proof`]).
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

    /// This report with every `Verified` step turned into an `Error` and every
    /// proof certificate dropped, for a context whose `Verified` answer cannot
    /// be published. A step's own answer proves no more than the function's,
    /// so a reader that walks the steps (obligation certificates, proven facts,
    /// optimization hints) must not find one. Other step results are kept.
    pub(crate) fn without_verified_steps(mut self) -> Self {
        for step in &mut self.steps {
            if step.result == StepResultKind::Verified {
                step.result = StepResultKind::Error;
                step.unknown = None;
            }
            #[cfg(feature = "proof-certificates")]
            {
                step.proof = None;
            }
        }
        #[cfg(feature = "proof-certificates")]
        {
            self.proof = None;
        }
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
    fn test_without_verified_steps_turns_only_verified_steps_into_errors() {
        let report = VerificationReport::from_parts(
            VerifyResult::Error {
                message: "refused".to_string(),
            },
            None,
            vec![
                step("overflow_check_0", StepResultKind::Verified),
                step("overflow_check_1", StepResultKind::Counterexample),
                step("timed_out", StepResultKind::Unknown),
                step("cleanup", StepResultKind::Skipped),
            ],
            Duration::from_millis(20),
        )
        .without_verified_steps();

        let results: Vec<_> = report.steps().iter().map(StepDiagnostic::result).collect();
        assert_eq!(
            results,
            vec![
                StepResultKind::Error,
                StepResultKind::Counterexample,
                StepResultKind::Unknown,
                StepResultKind::Skipped,
            ]
        );
        assert!(report.steps()[0].unknown().is_none());
        assert!(report.steps()[2].unknown().is_some());
    }

    #[test]
    fn test_first_non_verified_step_returns_first_counterexample() {
        let report = VerificationReport::from_parts(
            VerifyResult::Counterexample {
                obligation_name: "postcondition".to_string(),
                location: None,
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
