//! Public verification outcomes and convenience helpers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::UnknownCategory;
use crate::error::TrustVcError;

/// A variable or function binding from a counterexample model.
///
/// Provides structured access to variable names, types, and values
/// that violate a proof obligation. Used by IDE plugins, CI tools,
/// and JSON output consumers.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CounterexampleBinding {
    /// User-facing display name (e.g., `old(x)` instead of `__trust_vc_old_x`).
    pub display_name: String,
    /// Raw solver variable name.
    pub raw_name: String,
    /// Human-readable type (e.g., `i32`, `Seq<u64>`).
    pub ty: String,
    /// Rendered value (e.g., `-42`, `[1, 2, 3]`, or a function's formal parameters and body).
    pub value: String,
}

impl CounterexampleBinding {
    /// Creates a new counterexample binding.
    #[must_use]
    pub fn new(
        display_name: impl Into<String>,
        raw_name: impl Into<String>,
        ty: impl Into<String>,
        value: impl Into<String>,
    ) -> Self {
        Self {
            display_name: display_name.into(),
            raw_name: raw_name.into(),
            ty: ty.into(),
            value: value.into(),
        }
    }
}

/// Result of verifying a proof obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[must_use = "verification results must be checked — ignoring silently skips verification"]
pub enum VerifyResult {
    /// All obligations verified successfully.
    Verified,
    /// Found a counterexample - at least one obligation is violable.
    Counterexample {
        /// Which obligation failed. This is the obligation's NAME and nothing
        /// else: no source position, no rendered `file:line:column`, no
        /// prose. Consumers that match an obligation by name — the
        /// `proof_note`/`custom_err` diagnostic channel
        /// (`VerificationContext::apply_proof_note_verdict`), the certificate
        /// writer's per-obligation attribution, the corpus regression suites —
        /// compare against this directly. Gluing anything else in here is what
        /// silently removed the user-label capability once already; see
        /// `crates/trust-vc-core/tests/refuted_obligation_identity.rs`.
        obligation_name: String,
        /// WHERE the refutation is, as its OWN field: the rendered
        /// `file:line:column` of the refuted obligation, or `None` on a lane
        /// that records no position (the path-less entry point). A renderer
        /// that wants to show the position composes it with `obligation_name`
        /// itself; it is never composed for it.
        location: Option<String>,
        /// Variable assignments that violate the obligation (if available)
        model: Option<String>,
        /// Structured variable bindings from the counterexample model.
        bindings: Vec<CounterexampleBinding>,
    },
    /// The obligation was **not discharged**, and there is **no model**.
    ///
    /// This is the analogue of Verus's `ValidityResult::Invalid(None, None,
    /// None)` (air/smt_verify.rs): a genuine theory/decision-procedure
    /// *incompleteness* on a proof obligation is reported as a verification
    /// FAILURE rather than as a soft `Unknown`. See
    /// `docs/design-unknown-as-failure.md`.
    ///
    /// # Why a distinct variant (and not `Counterexample { model: None }`)
    ///
    /// The design's load-bearing property is "**no fabricated model, no
    /// fabricated counterexample narrative**". Encoding that as a
    /// `Counterexample` with an absent model would make the property a
    /// *convention* that every consumer has to remember to honour — and several
    /// would not: the report renderer prints an "obligation/model" block, the
    /// Trust engine adapter lowers `Counterexample` to `TrustOutcome::Refuted`
    /// with a model field, and the oracle lowers it to `ProofFeedback::Failed {
    /// counterexamples }`. Each would then present a refutation we never found.
    ///
    /// Making it a separate variant *with no `model` and no `bindings` field*
    /// moves the property from convention into the type system: it is
    /// structurally impossible to attach a counterexample to this outcome, or
    /// to read one out of it. `is_counterexample()` stays `false`.
    ///
    /// # Why no `obligation_name` field
    ///
    /// Every producer of an incompleteness category already embeds the
    /// obligation's name and location in `reason` (see
    /// `solve::solver_unknown_outcome`, which renders `... for '<name>' at
    /// <loc>`), and the internal `AssertionOutcome::Unknown` this is built from
    /// carries no separate name. A dedicated field would therefore be `None`
    /// at every construction site — a false affordance. `reason` is the naming
    /// channel.
    ///
    /// # Soundness boundary
    ///
    /// `category` is **always** an incompleteness-class category
    /// ([`UnknownCategory::is_incompleteness`]). A RESOURCE/timeout/cancellation
    /// unknown can never reach this variant — it stays [`Self::Unknown`],
    /// because a timeout does not mean the fact is false. That split is checked
    /// at the single construction point in `VerifyResult::unknown`.
    NotProved {
        /// Why the obligation could not be discharged. Carries the obligation
        /// name and location as rendered by the producer.
        reason: String,
        /// The incompleteness-class category that justified reporting this as a
        /// failure. Invariant: `category.is_incompleteness()` is `true`.
        category: UnknownCategory,
    },
    /// Solver could not determine satisfiability.
    ///
    /// Reserved for outcomes that are **not** a verdict on the obligation:
    /// resource exhaustion, timeout, cancellation, solver panics, and other
    /// inconclusive states where more budget (or a fix) might still decide it.
    /// A genuine theory incompleteness on an obligation is [`Self::NotProved`].
    Unknown {
        /// Reason for unknown result
        reason: String,
        /// Structured classification for programmatic triage.
        category: UnknownCategory,
    },
    /// Encoding error occurred.
    Error {
        /// Error message
        message: String,
    },
}

impl VerifyResult {
    /// The **single** construction point for both inconclusive outcomes, and
    /// therefore the one place the soundness boundary of
    /// `docs/design-unknown-as-failure.md` is enforced.
    ///
    /// A genuine theory/decision-procedure **incompleteness** on a proof
    /// obligation becomes [`VerifyResult::NotProved`] — a model-less
    /// verification FAILURE, matching Verus's `Invalid(None, None, None)`.
    /// Everything else — RESOURCE exhaustion, timeout, cancellation, solver
    /// panic, and any unrecognized reason — stays [`VerifyResult::Unknown`],
    /// because a timeout does not mean the fact is false.
    ///
    /// Routing here rather than at each producer is deliberate: it makes the
    /// boundary a single auditable branch that no caller can bypass, and it
    /// fails **open** (towards the soft `Unknown`) for every category except
    /// the one explicitly proven to be permanent.
    ///
    /// This is sound in both directions because `UnknownCategory::Incompleteness`
    /// is only ever produced by obligation-scoped code:
    /// `UnknownCategory::from_unknown_reason` (an ay verdict on an obligation
    /// query, reached via `solve::solver_unknown_outcome` and
    /// `overflow`), plus the four explicit fail-closed producers in
    /// `assertion.rs`, `typed_assertions.rs`, `split.rs`, and
    /// `trait_conformance.rs`. Notably `UnknownCategory::classify` — the
    /// string-based fallback used when no structured category is supplied —
    /// can never return `Incompleteness`, so an unclassified reason string
    /// cannot be promoted into a failure by accident.
    pub(crate) fn unknown(reason: impl Into<String>, category: Option<UnknownCategory>) -> Self {
        let reason = reason.into();
        let category = category.unwrap_or_else(|| UnknownCategory::classify(&reason));
        if category.is_incompleteness() {
            return Self::NotProved { reason, category };
        }
        Self::Unknown { reason, category }
    }

    /// Returns true if the proof was verified.
    #[must_use]
    pub const fn is_verified(&self) -> bool {
        matches!(self, VerifyResult::Verified)
    }

    /// Returns true if a counterexample **with a model** was found.
    ///
    /// Deliberately `false` for [`VerifyResult::NotProved`]: that outcome is a
    /// verification failure, but no counterexample was ever found for it. Use
    /// [`Self::is_failure`] to ask "did this obligation fail?".
    #[must_use]
    pub const fn is_counterexample(&self) -> bool {
        matches!(self, VerifyResult::Counterexample { .. })
    }

    /// Returns true if the obligation was not discharged because of a genuine
    /// theory/decision-procedure incompleteness — a model-less verification
    /// FAILURE. See [`VerifyResult::NotProved`].
    #[must_use]
    pub const fn is_not_proved(&self) -> bool {
        matches!(self, VerifyResult::NotProved { .. })
    }

    /// Returns true if this is a **verdict of failure** on the obligation:
    /// either a model-bearing counterexample or a model-less non-proof.
    ///
    /// This is the predicate to use when partitioning outcomes into
    /// pass/fail/inconclusive. `Unknown` is deliberately excluded — a timeout
    /// is not a failure — and so is `Error`, which is an infrastructure fault
    /// rather than a verdict.
    #[must_use]
    pub const fn is_failure(&self) -> bool {
        matches!(
            self,
            VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. }
        )
    }

    /// Returns true if the result is unknown (inconclusive, *not* a failure).
    ///
    /// Deliberately `false` for [`VerifyResult::NotProved`], which is a
    /// verdict of failure rather than an inconclusive outcome.
    #[must_use]
    pub const fn is_unknown(&self) -> bool {
        matches!(self, VerifyResult::Unknown { .. })
    }

    /// Returns true if an error occurred.
    #[must_use]
    pub const fn is_error(&self) -> bool {
        matches!(self, VerifyResult::Error { .. })
    }
}

impl From<TrustVcError> for VerifyResult {
    fn from(err: TrustVcError) -> Self {
        VerifyResult::Error {
            message: err.to_string(),
        }
    }
}
