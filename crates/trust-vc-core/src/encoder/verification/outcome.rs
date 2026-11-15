//! Internal verification outcome for single-assertion verification paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Separates verification outcomes (Verified, Counterexample, Unknown) from
//! infrastructure errors (TrustVcError). Previously these were conflated in
//! `Result<(bool, Option<String>), VerifyResult>` where `VerifyResult::Unknown`
//! and `VerifyResult::Error` appeared in the `Err` position alongside actual
//! verification results. Part of #1690.

use super::unknown_category::UnknownCategory;
use crate::encoder::types::VerifyResult;
use crate::verify_result::CounterexampleBinding;
use ay_dpll::UnknownReason;

/// Exact structured detail for solver-originated Unknown results.
///
/// Kept internal so trust_vc can retain solver-specific distinction for retry
/// policies without changing the public `VerifyResult` surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SolverUnknownDetail {
    AY(UnknownReason),
}

/// Classification used by adaptive retry logic for quantifier Unknown details.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum AdaptiveQuantifierRetryClass {
    /// Budget pressure that may recover with a larger quantifier budget.
    BudgetPressureRetriable,
    /// Capability/incompleteness gap that should not be retried.
    PermanentlyNonRetriable,
    /// Non-quantifier or currently unclassified unknown detail.
    Other,
}

impl SolverUnknownDetail {
    #[must_use]
    pub(crate) fn from_unknown_reason(reason: Option<UnknownReason>) -> Option<Self> {
        reason.map(Self::AY)
    }

    #[must_use]
    pub(crate) fn adaptive_quantifier_retry_class(self) -> AdaptiveQuantifierRetryClass {
        match self {
            Self::AY(UnknownReason::QuantifierRoundLimit | UnknownReason::QuantifierDeferred) => {
                AdaptiveQuantifierRetryClass::BudgetPressureRetriable
            }
            Self::AY(
                UnknownReason::QuantifierUnhandled
                | UnknownReason::QuantifierCegqiIncomplete
                | UnknownReason::QuantifierEmatchingExistsIncomplete,
            ) => AdaptiveQuantifierRetryClass::PermanentlyNonRetriable,
            Self::AY(_) => AdaptiveQuantifierRetryClass::Other,
        }
    }

    #[must_use]
    pub(crate) fn is_budget_retriable(self) -> bool {
        matches!(
            self.adaptive_quantifier_retry_class(),
            AdaptiveQuantifierRetryClass::BudgetPressureRetriable
        )
    }
}

/// Outcome of verifying a single assertion.
///
/// This is the internal outcome type used by the verification pipeline.
/// Infrastructure failures are handled separately via `TrustVcError`.
/// The public API still returns `VerifyResult` — see `From<AssertionOutcome>`.
#[derive(Debug, Clone)]
pub(crate) enum AssertionOutcome {
    /// The assertion was proved valid (solver returned Unsat for negation).
    Verified,
    /// A counterexample was found — the assertion is violable.
    Counterexample {
        /// The obligation's NAME. Never carries a source position — the
        /// position is `location`, beside it.
        obligation_name: String,
        /// The refuted obligation's rendered `file:line:column`, when the lane
        /// recorded one.
        location: Option<String>,
        /// Variable assignments that violate the obligation (if available).
        model: Option<String>,
        /// Structured variable bindings from the counterexample model.
        bindings: Vec<CounterexampleBinding>,
    },
    /// The solver could not determine satisfiability.
    Unknown {
        /// Human-readable reason for the unknown result.
        reason: String,
        /// Structured classification of the unknown reason.
        category: Option<UnknownCategory>,
        /// Exact solver detail retained for internal retry policy decisions.
        detail: Option<SolverUnknownDetail>,
    },
    /// A statically-decided rejection that is *not* a model-bearing
    /// counterexample (#2778).
    ///
    /// Mirrors upstream Verus, where an exec bit-shift whose shift amount has a
    /// *signed* type (and is therefore possibly negative) makes the obligation
    /// `0 <= b < width` undischargeable, surfacing as a VIR-level error
    /// (`assert_vir_error_msg`, i.e. an error with no diagnostic code) rather
    /// than an `assert_fails` counterexample. trust-vc reproduces that
    /// distinction by routing this failure to `VerifyResult::Error`. The
    /// underlying solver obligation is identical to the counterexample path, so
    /// a provably-in-range signed amount still verifies; only the *out-of-range*
    /// failure is reclassified, keeping the rejection strictly as sound as the
    /// counterexample it replaces.
    Error {
        /// Diagnostic message carrying the byte-exact upstream label
        /// (`possible bit shift underflow/overflow`).
        message: String,
    },
}

impl AssertionOutcome {
    pub(super) fn unknown(reason: impl Into<String>, category: Option<UnknownCategory>) -> Self {
        Self::unknown_with_detail(reason, category, None)
    }

    pub(super) fn unknown_with_detail(
        reason: impl Into<String>,
        category: Option<UnknownCategory>,
        detail: Option<SolverUnknownDetail>,
    ) -> Self {
        Self::Unknown {
            reason: reason.into(),
            category,
            detail,
        }
    }
}

impl From<AssertionOutcome> for VerifyResult {
    fn from(outcome: AssertionOutcome) -> Self {
        match outcome {
            AssertionOutcome::Verified => VerifyResult::Verified,
            AssertionOutcome::Counterexample {
                obligation_name,
                location,
                model,
                bindings,
            } => VerifyResult::Counterexample {
                obligation_name,
                location,
                model,
                bindings,
            },
            AssertionOutcome::Unknown {
                reason, category, ..
            } => VerifyResult::unknown(reason, category),
            AssertionOutcome::Error { message } => VerifyResult::Error { message },
        }
    }
}

#[cfg(test)]
#[path = "outcome_tests.rs"]
mod tests;
