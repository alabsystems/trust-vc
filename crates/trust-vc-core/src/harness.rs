//! Whole-harness (single proof fn) verification with `assert_one_fails`
//! semantics.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Motivation
//!
//! Upstream Verus tests routinely place several `assert(...)` statements inside
//! a *single* `proof fn`, where exactly one of them is expected to fail. The
//! upstream harness helper `assert_one_fails` then checks that the bundle
//! produced **exactly one** verification failure (on the line marked `FAILS`)
//! while every other assertion verified. The canonical example is the
//! `real_basics` test:
//!
//! ```text
//! proof fn test(i: int, x: real, y: real) {
//!     assert(x == 0.2real ==> x / 2.0 == 0.1real);   // passes
//!     assert(x > 0.0 ==> x / 3.0 > 0.0);             // passes
//!     ...
//!     assert(x >= 0.0 ==> x / 3.0 > 0.0);            // FAILS
//! }
//! ```
//!
//! Reproducing this faithfully — as **one** case rather than a fragmented set
//! of single-assert functions — requires modeling the proof fn as a whole:
//! verify each assertion in source order, accumulating each *verified*
//! assertion as a fact available to later assertions (faithful Verus
//! sequential semantics), then report how many assertions failed and which one.
//!
//! # Soundness
//!
//! Sequential accumulation only ever assumes assertions that have **already
//! verified**. A verified assertion is a proven fact under the harness's
//! preconditions, so assuming it for a later assertion is sound — it is exactly
//! the knowledge Verus carries forward. A *failed* assertion is never assumed
//! (it was not proven), so it cannot mask a downstream failure. Each assertion
//! is therefore discharged under precisely the facts it would have in Verus,
//! and `assert_one_fails` is satisfied iff exactly one assertion is a
//! counterexample.

use crate::vc::{ObligationKind, ProofObligation, VerificationContext};
use crate::VerifyResult;

/// Returns true when `kind` denotes a *bundled harness assertion* — a goal the
/// harness discharges in source order, as opposed to background context it
/// merely assumes.
///
/// This is the plain `assert(...)` obligation kind ([`ObligationKind::Assert`]).
/// Note that `assert(...) by(bit_vector)` is **also** an
/// [`ObligationKind::Assert`] — it differs only by carrying
/// `solver_mode = SolverMode::BitVector` (see [`ProofObligation::solver_mode`]),
/// so a `by(bit_vector)` bundle flows through this same path and is discharged
/// against the bit-vector theory, never assumed. (`ObligationKind::AssertBy`,
/// by contrast, is `assert ... by { proof_block }`, which is discharged inside a
/// separately *prepared* proof scope and is therefore not a standalone bundle
/// goal; it is left in the background here and is out of scope for whole-case
/// `assert_fails(err, N)` bundling.)
#[must_use]
fn is_bundled_assertion(kind: ObligationKind) -> bool {
    matches!(kind, ObligationKind::Assert)
}

/// Per-assertion outcome inside a whole-harness verification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct HarnessAssertion {
    /// Zero-based position of this assertion among the harness assertions
    /// (in source order).
    pub index: usize,
    /// The assertion obligation's name.
    pub name: String,
    /// Source location (file:line:col), when the obligation carried one.
    pub location: Option<String>,
    /// The verifier verdict for this single assertion.
    pub result: VerifyResult,
}

impl HarnessAssertion {
    /// Returns true when this assertion was discharged as a counterexample.
    #[must_use]
    pub fn is_counterexample(&self) -> bool {
        self.result.is_counterexample()
    }
}

/// Outcome of verifying a whole proof-fn harness.
///
/// Distinguishes the three verdicts that matter for upstream harness helpers:
/// all assertions verified ([`Self::AllVerified`]), exactly one assertion
/// failed ([`Self::OneFailed`], matching `assert_one_fails`), or several
/// assertions failed ([`Self::MultipleFailed`], matching `assert_fails(n)`).
/// Solver-inconclusive results are surfaced separately so they never silently
/// pass as success.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[must_use = "harness outcomes must be checked — ignoring one silently skips verification"]
pub enum HarnessOutcome {
    /// Every harness assertion verified.
    AllVerified {
        /// Number of assertions that were checked.
        assertions: usize,
    },
    /// Exactly one harness assertion failed; all others verified.
    ///
    /// This is the outcome that reproduces upstream `assert_one_fails`.
    OneFailed {
        /// The failing assertion.
        failure: HarnessAssertion,
        /// Total number of assertions that were checked.
        assertions: usize,
    },
    /// More than one harness assertion failed.
    MultipleFailed {
        /// Every assertion that produced a counterexample, in source order.
        failures: Vec<HarnessAssertion>,
        /// Total number of assertions that were checked.
        assertions: usize,
    },
    /// The solver could not decide some assertion (returned `Unknown`) or an
    /// encoding error occurred. Carries the first such assertion so callers
    /// fail closed rather than mistaking it for a clean pass or a clean fail.
    Inconclusive {
        /// The first assertion that returned `Unknown` or `Error`.
        assertion: HarnessAssertion,
    },
}

impl HarnessOutcome {
    /// Returns true when **exactly one** assertion failed and all others
    /// verified — the faithful reproduction of upstream `assert_one_fails`.
    #[must_use]
    pub fn asserts_one_fails(&self) -> bool {
        matches!(self, HarnessOutcome::OneFailed { .. })
    }

    /// Returns true when every assertion verified.
    #[must_use]
    pub fn all_verified(&self) -> bool {
        matches!(self, HarnessOutcome::AllVerified { .. })
    }

    /// Returns true when exactly `count` assertions failed and the rest
    /// verified — the faithful reproduction of upstream `assert_fails(count)`.
    #[must_use]
    pub fn asserts_n_fail(&self, count: usize) -> bool {
        self.failure_count() == count && !self.is_inconclusive()
    }

    /// Total number of bundled assertions (`K`) the harness discharged.
    ///
    /// This is every `assert(...)` and `assert(...) by(bit_vector)` obligation
    /// in the proof fn — the bundle size the upstream `assert_fails(err, N)`
    /// helper localizes against. Returns 0 for an inconclusive outcome (the
    /// bundle was abandoned at the first undecided step).
    #[must_use]
    pub fn total_assertions(&self) -> usize {
        match self {
            HarnessOutcome::AllVerified { assertions }
            | HarnessOutcome::OneFailed { assertions, .. }
            | HarnessOutcome::MultipleFailed { assertions, .. } => *assertions,
            HarnessOutcome::Inconclusive { .. } => 0,
        }
    }

    /// Number of bundled assertions that verified, i.e. `K - N`.
    ///
    /// Together with [`Self::failure_count`] (`N`) and [`Self::total_assertions`]
    /// (`K`) this is the complete localization upstream `assert_fails(err, N)`
    /// checks: exactly `N` counterexamples and `K - N` verified. Returns 0 for
    /// an inconclusive outcome.
    #[must_use]
    pub fn verified_count(&self) -> usize {
        // Saturating guards against any future variant where the failure count
        // could exceed the recorded bundle size; today they are always
        // consistent by construction.
        self.total_assertions().saturating_sub(self.failure_count())
    }

    /// Faithful whole-case reproduction of upstream `assert_fails(err, fails)`
    /// for a `total`-obligation bundle: **exactly** `fails` counterexamples,
    /// **exactly** `total - fails` verified, and a conclusive verdict
    /// (no `Unknown`/`Error` step).
    ///
    /// This is the single predicate a ported `assert_fails(err, N)` case should
    /// assert. It strengthens [`Self::asserts_n_fail`] by also pinning the
    /// bundle size `K`, so a port cannot silently drop or gain obligations and
    /// still pass — the localization must match upstream exactly.
    #[must_use]
    pub fn matches_assert_fails(&self, total: usize, fails: usize) -> bool {
        !self.is_inconclusive()
            && self.total_assertions() == total
            && self.failure_count() == fails
            && self.verified_count() == total.saturating_sub(fails)
    }

    /// Returns true when the harness was solver-inconclusive (`Unknown`) or hit
    /// an encoding error on some assertion.
    #[must_use]
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, HarnessOutcome::Inconclusive { .. })
    }

    /// Number of assertions that produced a counterexample.
    ///
    /// Returns 0 for an inconclusive outcome (no definite failure count is
    /// available).
    #[must_use]
    pub fn failure_count(&self) -> usize {
        match self {
            HarnessOutcome::AllVerified { .. } => 0,
            HarnessOutcome::OneFailed { .. } => 1,
            HarnessOutcome::MultipleFailed { failures, .. } => failures.len(),
            HarnessOutcome::Inconclusive { .. } => 0,
        }
    }
}

impl VerificationContext {
    /// Verifies this context as a whole proof-fn harness, reporting how many
    /// assertions failed (and which) as a single [`HarnessOutcome`].
    ///
    /// Assertions are discharged in source order. Every assertion that verifies
    /// is carried forward as an assumption for the remaining assertions, exactly
    /// as Verus accumulates proven facts within a `proof fn` body. Failed
    /// assertions are never assumed, so they cannot mask later failures.
    ///
    /// Non-assertion obligations (assumptions, preconditions, etc.) form the
    /// shared background available to every assertion and are left untouched.
    ///
    /// See the module docs for the soundness argument.
    pub fn verify_harness(&self) -> HarnessOutcome {
        let assertion_indices: Vec<usize> = self
            .obligations()
            .iter()
            .enumerate()
            .filter(|(_, ob)| is_bundled_assertion(ob.kind()))
            .map(|(idx, _)| idx)
            .collect();

        // Background obligations are everything that is not a bundled harness
        // assertion: assumptions, preconditions, broadcast assumptions, etc.
        // `by(bit_vector)` goals are `Assert`-kind (with a bit-vector solver
        // mode), so they are picked up as assertions above and discharged below,
        // never assumed.
        let background: Vec<ProofObligation> = self
            .obligations()
            .iter()
            .filter(|ob| !is_bundled_assertion(ob.kind()))
            .cloned()
            .collect();

        let mut failures: Vec<HarnessAssertion> = Vec::new();
        // Assertions proven so far, lowered to assumptions for later steps.
        let mut proven_facts: Vec<ProofObligation> = Vec::new();

        for (position, &obligation_idx) in assertion_indices.iter().enumerate() {
            let assertion = &self.obligations()[obligation_idx];

            let derived =
                self.derive_single_assertion_context(&background, &proven_facts, assertion);
            let result = derived.verify();

            let harness_assertion = HarnessAssertion {
                index: position,
                name: assertion.name().to_string(),
                location: assertion.location().map(str::to_string),
                result: result.clone(),
            };

            match result {
                VerifyResult::Verified => {
                    // Carry this proven fact forward to later assertions.
                    proven_facts.push(assertion_as_assumption(assertion));
                }
                // Both are verdicts of FAILURE on this assertion, so both count
                // toward the harness failure tally. `NotProved` is the
                // model-less incompleteness failure — the analogue of Verus's
                // `Invalid(None, None, None)`, which likewise contributes an
                // error span to `assert_one_fails` without any model being
                // inspected (see `docs/design-unknown-as-failure.md`).
                VerifyResult::Counterexample { .. } | VerifyResult::NotProved { .. } => {
                    failures.push(harness_assertion);
                }
                VerifyResult::Unknown { .. } | VerifyResult::Error { .. } => {
                    // Fail closed: do not let an inconclusive step pass as a
                    // success or as a definite failure.
                    return HarnessOutcome::Inconclusive {
                        assertion: harness_assertion,
                    };
                }
            }
        }

        let assertions = assertion_indices.len();
        match failures.len() {
            0 => HarnessOutcome::AllVerified { assertions },
            1 => HarnessOutcome::OneFailed {
                failure: failures.pop().expect("invariant: exactly one failure"),
                assertions,
            },
            _ => HarnessOutcome::MultipleFailed {
                failures,
                assertions,
            },
        }
    }

    /// Builds a derived context that keeps the shared background and all
    /// previously proven assertions (lowered to assumptions), with exactly the
    /// single `assertion` left to verify.
    ///
    /// The derived context inherits every configuration field of `self`
    /// (variables, overflow policy, function context, trait/struct registries,
    /// …) by cloning, so per-assertion verification sees the same environment
    /// as the whole-harness proof fn.
    fn derive_single_assertion_context(
        &self,
        background: &[ProofObligation],
        proven_facts: &[ProofObligation],
        assertion: &ProofObligation,
    ) -> VerificationContext {
        let mut derived = self.clone();
        let mut obligations = Vec::with_capacity(background.len() + proven_facts.len() + 1);
        obligations.extend(background.iter().cloned());
        obligations.extend(proven_facts.iter().cloned());
        obligations.push(assertion.clone());
        derived.obligations = obligations;
        derived
    }
}

/// Lowers a verified assertion into an assumption obligation carrying the same
/// condition payload (typed expression when present, else the string
/// condition). Sound because the assertion has already been proven.
fn assertion_as_assumption(assertion: &ProofObligation) -> ProofObligation {
    let name = format!("__harness_proven_{}", assertion.name());
    let mut assumption = if let Some(expr) = assertion.typed_expr() {
        ProofObligation::new_typed(name, expr.clone(), ObligationKind::Assume)
    } else {
        ProofObligation::assume(name, assertion.condition())
    };
    if let Some(location) = assertion.location() {
        assumption = assumption.with_location(location);
    }
    assumption
}

#[cfg(test)]
mod tests;
