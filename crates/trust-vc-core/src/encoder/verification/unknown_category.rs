//! Actionable classification of Unknown verification results.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Derived from either structured `UnknownReason` values or the string
//! `reason` field of `VerifyResult::Unknown`. Enables programmatic triage
//! from the public verification result surface.
//! Part of #2259.

use super::panic::is_sort_mismatch_error;
use crate::encoder::types::VerifyResult;
use ay_dpll::UnknownReason;

/// Actionable classification of Unknown verification results.
///
/// Each variant maps to a category of `VerifyResult::Unknown` reason strings
/// produced by the verification pipeline (assertion.rs, typed.rs, panic.rs).
/// Enables programmatic triage, retry decisions, and telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UnknownCategory {
    /// BV/general solver timeout — may succeed with longer timeout
    Timeout,
    /// ay-dpll internal panic caught by catch_unwind
    SolverPanic,
    /// Solver thread panicked outside ay (programmer error that was caught)
    ThreadPanic,
    /// Confirmation check disagreed — possible non-determinism
    ConfirmationDisagree,
    /// ay Sat result with unvalidated model — spurious counterexample
    ModelNotValidated,
    /// Sat with empty model — CEGQI limitation on quantified assertions
    EmptyModel,
    /// Solver returned Unknown for a RESOURCE reason (timeout-adjacent budget /
    /// round / split exhaustion). A timeout does NOT mean the fact is false —
    /// more resources might prove it — so this is reported as a non-failure
    /// `Unknown`, never as a verification failure. This is the load-bearing
    /// soundness boundary opposite [`Self::Incompleteness`].
    SolverUnknown,
    /// Solver returned Unknown for a genuine THEORY-INCOMPLETENESS reason: the
    /// fact may be valid, but the available decision procedure cannot decide it
    /// (NRA/nonlinear, unsupported fragment, or a permanently-non-retriable
    /// triggerless / CEGQI / e-matching quantifier gap). Distinct from
    /// [`Self::SolverUnknown`] because, unlike a resource limit, *no* amount of
    /// extra budget closes the gap. On a proof obligation this is surfaced as a
    /// model-less verification FAILURE — the conservative, Verus-faithful
    /// reading (Verus maps Z3's incompleteness `unknown` to
    /// `Invalid(None, None, None)`, an assert-fails outcome with no model). See
    /// `design-unknown-as-failure.md`.
    Incompleteness,
    /// ay's INDEPENDENT MODEL-CHECK GATE refuted the model ay had just
    /// produced, and ay fail-closed `Sat -> Unknown`.
    ///
    /// This is the THIRD category, and it is neither of the other two halves of
    /// the `design-unknown-as-failure.md` split:
    ///
    /// * it is NOT a refutation of the user's proof — nothing showed the
    ///   obligation false; a candidate *witness* was shown false;
    /// * it is NOT a resource limit — no amount of budget changes it (the
    ///   trigger measured on 2026-09-17 is deterministic, 15/15 runs);
    /// * it is NOT a theory incompleteness either — the decision procedure did
    ///   produce an answer, and then ay's own gate caught that answer being
    ///   wrong.
    ///
    /// The solver found a model, could not independently confirm it, and
    /// refused to publish it. That is ay behaving CORRECTLY (a caught internal
    /// solver bug, fail-closed), and it is the one thing the user's own proof
    /// text cannot be blamed for.
    ///
    /// # Why this still routes to a FAILURE
    ///
    /// [`Self::is_incompleteness`] is `true` for this variant, so it lands on
    /// [`crate::VerifyResult::NotProved`] exactly as
    /// [`Self::Incompleteness`] does, and **no verdict moves**. That is
    /// deliberate: the obligation genuinely was not discharged and must fail
    /// closed. What this variant changes is WHICH failure the user is told
    /// about — `actionable_suggestion` and the rendered detail line say the
    /// solver caught its own invalid model, instead of asserting that the
    /// proof is wrong.
    ///
    /// # Provenance
    ///
    /// Detected from ay's own attribution on the same solve envelope:
    /// `unknown.phase == "independent-model-check-gate"` (also carried typed on
    /// `SolveDetails::unknown_diagnostic.phase`) or
    /// `model_check_gate.result == "model-violates"`. See
    /// `docs/ay-defect-2026-09-17-quantified-axiom-family.md`.
    ModelGateRejected,
    /// Encoding used approximations that make Verified unreliable
    EncodingDemotion,
    /// Variables have types that cannot be soundly encoded
    OpaqueTypes,
    /// Assumptions are contradictory (vacuous truth)
    VacuousTruth,
    /// Requested solver mode not implemented
    UnsupportedMode,
    /// Unrecognized reason string
    Other,
}

impl UnknownCategory {
    /// Map a structured ay unknown reason into the existing trust_vc categories.
    ///
    /// The split between [`Self::Incompleteness`] and [`Self::SolverUnknown`] is
    /// the load-bearing soundness boundary (`design-unknown-as-failure.md`):
    ///
    /// * **Incompleteness** — a genuine theory/decision-procedure gap where *no*
    ///   amount of extra resource closes the gap (NRA/nonlinear `Incomplete`,
    ///   unsupported fragments, `ExpressionSplit` (unimplemented), and the
    ///   permanently-non-retriable quantifier reasons). On a proof obligation
    ///   this becomes a model-less verification FAILURE, matching Verus's
    ///   `Invalid(None, None, None)` for Z3-incompleteness `unknown`.
    /// * **SolverUnknown / Timeout** — a RESOURCE/budget limit (timeout, rlimit,
    ///   memory, interruption, split-limit, and the budget-retriable quantifier
    ///   reasons `QuantifierRoundLimit` / `QuantifierDeferred`). A timeout does
    ///   not mean the fact is false, so these stay a non-failure `Unknown`.
    ///
    /// The quantifier classification mirrors `SolverUnknownDetail`'s existing
    /// `BudgetPressureRetriable` vs `PermanentlyNonRetriable` split in
    /// `outcome.rs` (the single source of truth for retriability).
    ///
    /// The wildcard catch-all is required because `UnknownReason` is from ay-dpll
    /// (external crate, `#[non_exhaustive]`). New ay-dpll variants default to
    /// `SolverUnknown` (fail-OPEN for the failure mapping: an unrecognized reason
    /// is never treated as an incompleteness failure, only as a soft `Unknown`).
    /// Review new ay-dpll `UnknownReason` variants on each bump to check if any
    /// should map to `Timeout`, `Incompleteness`, or another specific category.
    #[must_use]
    pub fn from_unknown_reason(reason: Option<UnknownReason>) -> Option<Self> {
        reason.map(|reason| match reason {
            UnknownReason::Timeout => Self::Timeout,
            // Genuine theory incompleteness — unprovable in the available
            // decision procedure regardless of resource budget.
            UnknownReason::Incomplete
            | UnknownReason::QuantifierUnhandled
            | UnknownReason::QuantifierCegqiIncomplete
            | UnknownReason::QuantifierEmatchingExistsIncomplete
            | UnknownReason::ExpressionSplit
            | UnknownReason::Unsupported
            | UnknownReason::UnsupportedArithmetic
            | UnknownReason::UnsupportedMixedCollection => Self::Incompleteness,
            // Resource / budget exhaustion — more budget might decide it.
            UnknownReason::ResourceLimit
            | UnknownReason::MemoryLimit
            | UnknownReason::Interrupted
            | UnknownReason::QuantifierRoundLimit
            | UnknownReason::QuantifierDeferred
            | UnknownReason::SplitLimit
            // InternalError / SelfCheckRejected / ProofTrusted / Unknown are
            // deliberately NOT incompleteness: an internal error, a verdict ay's
            // own gates declined to certify, an unsat whose proof ay would not
            // stand behind, or a reason-less unknown must never be reported as a
            // verification failure (fail-open to a soft Unknown).
            //
            // These are TWO variants again, not one. ay 0.6 (66538b006) deleted
            // `ProofTrusted` and left `SelfCheckRejected` carrying both facts;
            // ay 0.7 restored it at its original spelling, and ay's own docs now
            // insist on the distinction: `SelfCheckRejected` is the mandatory
            // certification funnel REFUTING a verdict it could not certify,
            // while `ProofTrusted` is the strict-proof gate WITHHOLDING an unsat
            // whose derivation chain is not independently checkable (a `trust`/
            // `hole` step or an unbacked `assume` leaf reaches the empty clause).
            // Both land in this arm, so the categorisation did not move across
            // the bump — but do not re-merge the comment: they are different
            // gates and a future arm may want to split them.
            //
            // ay's doc calls each occurrence "a LATENT WRONG ANSWER" — DO NOT
            // take that at face value. ay's own measurement contradicts it
            // (~86% of self-check unknowns agree with z3), and the three
            // occurrences chased down on 2026-08-08 were all ay-side defects
            // with CORRECT verdicts underneath: an `or`-step premise built with
            // a simplifying constructor (ay 028b53d91), a certified-default
            // model row aliasing the all-zeros point (ay 9ddf1283d), and a
            // nested re-solve forging the authored assertion epoch (ay
            // 0937e0b18), and a fourth on 2026-08-21 (ay: a certified
            // constant-`true` vacuous-quantifier collapse still set the
            // conservative translation-incomplete marker, whose read site then
            // downgraded a computed UNSAT to `Unknown(UnhandledQuantifier)` and
            // starved the deferred-trust discharge's corroboration re-solve).
            //
            // To see WHICH gate refused: there is NO `AY_PROBE_CERT_REJECT` env
            // var — ay retired the `AY_*` fallbacks for its diagnostic carriers
            // and `init_misc_cli_flags_from_env` deliberately keeps none. The
            // supported seam for a library embedder is the typed, process-wide
            // `ay_core::set_global_misc_cli_flags_with(|f| f.probe_cert_reject
            // = true)`, called once before the first solve (it is
            // first-writer-wins and returns `false` if the flags are already
            // initialized). From the `ay` CLI the flag is `--probe-cert-reject`.
            //
            // SolverUnknown is correct and SOUND either way: an uncertified
            // verdict is not a proof and must not discharge an obligation.
            | UnknownReason::InternalError
            | UnknownReason::SelfCheckRejected
            | UnknownReason::ProofTrusted
            | UnknownReason::Unknown
            | _ => Self::SolverUnknown,
        })
    }

    /// Classify an Unknown reason string into an actionable category.
    #[must_use]
    pub fn classify(reason: &str) -> Self {
        // MARKER BEFORE HEURISTIC. The confirmation sites emit a fixed
        // prefix and now quote the re-solve's own outcome after it
        // (`encoder/verification/assertion.rs`,
        // `encoder/verification/confirmation.rs`), so a quoted
        // "Solver returned unknown (timeout)" would otherwise make this
        // fall-back classifier read a confirmation failure as a plain
        // Timeout — and Timeout is the retriable category. The generated
        // prefix is unambiguous where a substring of the quoted reason is
        // not, so it is tested first. (Callers that already carry a typed
        // category never reach here; this is the recovery path for a bare
        // reason string.)
        if reason.contains("Confirmation check disagreed")
            || reason.contains("Confirmation check encoder error")
        {
            Self::ConfirmationDisagree
        } else if reason.contains("timed out")
            || reason.contains("Solver returned unknown (timeout)")
        {
            Self::Timeout
        } else if is_sort_mismatch_error(reason)
            || reason.contains("ay solver panic")
            || reason.contains("ay panic during")
            || reason.contains("Confirmation check ay panic")
        {
            Self::SolverPanic
        } else if reason.contains("Solver thread panicked") {
            Self::ThreadPanic
        } else if reason.contains("model not validated") {
            Self::ModelNotValidated
        } else if reason.contains("empty model") {
            Self::EmptyModel
        } else if reason.contains("Solver returned unknown") {
            Self::SolverUnknown
        } else if reason.starts_with("demoted:") {
            Self::EncodingDemotion
        } else if reason.contains("unrecognized types") {
            Self::OpaqueTypes
        } else if reason.contains("contradictory") || reason.contains("vacuously true") {
            Self::VacuousTruth
        } else if reason.contains("not yet implemented") {
            Self::UnsupportedMode
        } else {
            Self::Other
        }
    }

    /// Whether this Unknown category is retriable with a longer timeout.
    ///
    /// Exhaustive match: new variants must be explicitly classified.
    #[must_use]
    pub fn is_retriable(&self) -> bool {
        match self {
            Self::Timeout => true,
            Self::SolverPanic
            | Self::ThreadPanic
            | Self::ConfirmationDisagree
            | Self::ModelNotValidated
            | Self::EmptyModel
            | Self::SolverUnknown
            | Self::Incompleteness
            // Deterministic in every run measured on 2026-09-17 (15/15 on the
            // two corpus files, 3 banners per affected function whether the
            // goal is valid or genuinely false): a retry buys nothing.
            | Self::ModelGateRejected
            | Self::EncodingDemotion
            | Self::OpaqueTypes
            | Self::VacuousTruth
            | Self::UnsupportedMode
            | Self::Other => false,
        }
    }

    /// Whether this Unknown is a genuine theory/decision-procedure
    /// incompleteness (the fact may be valid but is unprovable in the available
    /// theory) rather than a resource/budget limit.
    ///
    /// On a proof obligation this is surfaced as a model-less verification
    /// FAILURE (the conservative, Verus-faithful reading). Resource-class
    /// unknowns return `false` and stay a non-failure `Unknown`. See
    /// `design-unknown-as-failure.md`.
    ///
    /// Exhaustive match: new variants must be explicitly classified.
    #[must_use]
    pub fn is_incompleteness(&self) -> bool {
        match self {
            // BOTH route to the model-less FAILURE outcome
            // (`VerifyResult::NotProved`), and for the same reason: the
            // obligation was not discharged and no counterexample model may be
            // shown for it. They are NOT the same diagnosis — see
            // `Self::ModelGateRejected` — and the user-facing rendering splits
            // them; only the verdict routing is shared, which is what keeps
            // this a reporting fix with no verdict movement.
            Self::Incompleteness | Self::ModelGateRejected => true,
            Self::Timeout
            | Self::SolverPanic
            | Self::ThreadPanic
            | Self::ConfirmationDisagree
            | Self::ModelNotValidated
            | Self::EmptyModel
            | Self::SolverUnknown
            | Self::EncodingDemotion
            | Self::OpaqueTypes
            | Self::VacuousTruth
            | Self::UnsupportedMode
            | Self::Other => false,
        }
    }

    /// Whether this Unknown suggests a potential soundness issue.
    ///
    /// Exhaustive match: new variants must be explicitly classified.
    #[must_use]
    pub fn is_soundness_relevant(&self) -> bool {
        match self {
            // `ModelGateRejected` is soundness-RELEVANT in the same sense as
            // `ConfirmationDisagree`: a solver that produced a model it then
            // refuted has an internal defect worth chasing. It is NOT a
            // soundness FAILURE here — the gate fail-closed, which is the
            // system working — but it must be countable, and
            // `is_soundness_relevant` is the channel that counts it.
            Self::ConfirmationDisagree
            | Self::ModelGateRejected
            | Self::ModelNotValidated
            | Self::VacuousTruth
            | Self::EncodingDemotion => true,
            Self::Timeout
            | Self::SolverPanic
            | Self::ThreadPanic
            | Self::EmptyModel
            | Self::SolverUnknown
            | Self::Incompleteness
            | Self::OpaqueTypes
            | Self::UnsupportedMode
            | Self::Other => false,
        }
    }

    /// Whether this Unknown is a known ay-dpll limitation (not a trust_vc bug).
    ///
    /// Exhaustive match: new variants must be explicitly classified.
    #[must_use]
    pub fn is_solver_limitation(&self) -> bool {
        match self {
            Self::Timeout
            | Self::EmptyModel
            | Self::SolverUnknown
            | Self::Incompleteness
            // An ay-side defect by construction: the gate that fired is ay's
            // own, and the model it refuted was ay's own. Nothing in the user's
            // proof text or in trust-vc's encoding is implicated.
            | Self::ModelGateRejected
            | Self::SolverPanic => true,
            Self::ThreadPanic
            | Self::ConfirmationDisagree
            | Self::ModelNotValidated
            | Self::EncodingDemotion
            | Self::OpaqueTypes
            | Self::VacuousTruth
            | Self::UnsupportedMode
            | Self::Other => false,
        }
    }

    /// Short actionable next step for this unknown category.
    #[must_use]
    pub fn actionable_suggestion(&self) -> &'static str {
        match self {
            Self::Timeout => "Retry with a larger rlimit or inspect verbose solver stats.",
            Self::SolverPanic => {
                "Inspect the verbose report for solver details and reduce the failing obligation."
            }
            Self::ThreadPanic => {
                "Re-run with verbose reporting and inspect the surrounding verification thread setup."
            }
            Self::ConfirmationDisagree => {
                "Treat this as soundness-relevant and inspect retry or confirmation logic."
            }
            Self::ModelNotValidated => {
                "Do not trust the model; re-run with proof or model validation enabled."
            }
            Self::EmptyModel => {
                "Treat this as a solver limitation and inspect quantified obligations or triggers."
            }
            Self::SolverUnknown => {
                "Inspect quantifier counts, trigger-heavy obligations, and verbose solver stats."
            }
            Self::Incompleteness => {
                "The decision procedure cannot decide this (e.g. nonlinear arithmetic); \
                 supply an explicit proof (by(nonlinear_arith) / lemma) — it will not verify as-is."
            }
            Self::ModelGateRejected => {
                "Not a refutation of your proof: the solver produced a model it could not \
                 independently confirm and fail-closed. This is an ay-side defect \
                 (docs/ay-defect-2026-09-17-quantified-axiom-family.md); the obligation is \
                 undecided, not disproved."
            }
            Self::EncodingDemotion => {
                "Inspect encoding approximations before trusting a proved result."
            }
            Self::OpaqueTypes => {
                "Replace unsupported types with modeled ghost data or add a sound encoding."
            }
            Self::VacuousTruth => {
                "Check requires or assume constraints for contradiction before trusting the proof."
            }
            Self::UnsupportedMode => {
                "Switch to a supported solver mode or add the missing implementation."
            }
            Self::Other => "Inspect the raw unknown reason and verbose solver stats.",
        }
    }
}

impl VerifyResult {
    /// Return the stored Unknown category if this is an Unknown result.
    ///
    /// Returns `None` for non-Unknown variants (Verified, Counterexample, Error).
    #[must_use]
    pub fn unknown_category(&self) -> Option<UnknownCategory> {
        match self {
            // `NotProved` is a verification FAILURE rather than an inconclusive
            // outcome, but it still carries the incompleteness category that
            // justified that classification — surfacing it keeps the
            // category/suggestion diagnostics (and any triage tooling) working,
            // and makes the soundness boundary auditable at the consumer.
            Self::Unknown { category, .. } | Self::NotProved { category, .. } => Some(*category),
            _ => None,
        }
    }
}

#[cfg(test)]
#[path = "unknown_category_tests.rs"]
mod tests;
