//! Concrete verification boundary for `VerificationContext`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This is the only module under `vc/` that should depend on `crate::encoder`.

use super::VerificationContext;
use crate::encoder::AYEncoder;
use crate::prepared_context::prepare_context;
use crate::verification_report::{capture_report, VerificationReport, VerificationReportOptions};
use crate::VerifyResult;

const EMPTY_CONTEXT_MESSAGE: &str = "Cannot verify empty context: no obligations to check";

impl VerificationContext {
    /// Verify all obligations in this context, returning a [`VerifyResult`].
    ///
    /// This is the primary entry point for verification. It encodes the
    /// context into SMT via the internal ay encoder and checks satisfiability.
    pub fn verify(&self) -> VerifyResult {
        self.verify_internal()
    }

    /// Verify all obligations and return a [`VerificationReport`] with
    /// detailed diagnostics (per-step timing, solver statistics, and
    /// optional proof certificates).
    ///
    /// When this context carries a `verified_refusal`, no step of the report
    /// is `Verified` and it carries no proof certificate: the refusal covers
    /// each obligation, not only the function's result.
    pub fn verify_with_report(&self, _options: VerificationReportOptions) -> VerificationReport {
        let report = capture_report(None, || self.verify_internal_uncached());
        if self.verified_refusal.is_some() {
            report.without_verified_steps()
        } else {
            report
        }
    }

    fn verify_internal(&self) -> VerifyResult {
        // SOUNDNESS-CRITICAL (closure def-side isolation): a spec-carrying
        // `trust_vc::closure!` whose independent def-side VC failed during
        // extraction fails this function CLOSED. The failure was discharged in
        // an isolated child context and DISCARDED; only this non-verifying
        // verdict crossed back, so no closure hypothesis ever entered this
        // parent's obligations. See `VerificationContext::closure_def_side_failure`.
        if let Some(failure) = &self.closure_def_side_failure {
            return failure.clone();
        }
        if let Some(failure) = &self.source_catalog_termination_failure {
            return failure.clone();
        }
        if !self.has_assertions() && !self.has_assumptions() {
            return VerifyResult::Error {
                message: EMPTY_CONTEXT_MESSAGE.to_string(),
            };
        }

        self.apply_verified_refusal(self.apply_proof_note_verdict(AYEncoder::verify(self)))
    }

    fn verify_internal_uncached(&self) -> VerifyResult {
        // SOUNDNESS-CRITICAL (closure def-side isolation): a spec-carrying
        // `trust_vc::closure!` whose independent def-side VC failed during
        // extraction fails this function CLOSED. The failure was discharged in
        // an isolated child context and DISCARDED; only this non-verifying
        // verdict crossed back, so no closure hypothesis ever entered this
        // parent's obligations. See `VerificationContext::closure_def_side_failure`.
        if let Some(failure) = &self.closure_def_side_failure {
            return failure.clone();
        }
        if let Some(failure) = &self.source_catalog_termination_failure {
            return failure.clone();
        }
        if !self.has_assertions() && !self.has_assumptions() {
            return VerifyResult::Error {
                message: EMPTY_CONTEXT_MESSAGE.to_string(),
            };
        }

        let prepared = match prepare_context(self) {
            Ok(prepared) => prepared,
            Err(err) => return VerifyResult::from(err),
        };

        self.apply_verified_refusal(
            self.apply_proof_note_verdict(AYEncoder::verify_prepared_inner(&prepared)),
        )
    }

    /// Verus diagnostic-parity channel for user-labeled failing obligations
    /// (`#[verifier::proof_note("…")]` / `custom_err`, basic.rs FAMILY C).
    ///
    /// Upstream, EVERY verification failure is rendered as a compiler error;
    /// a failing obligation that carries a `proof_note` label gets a
    /// secondary "note: {text}" span label on the unchanged primary failure
    /// diagnostic (`rust_verify/src/verifier.rs:96-140`), and a `custom_err`
    /// label REPLACES the primary message. The upstream test harness
    /// classifies both through `assert_help_error_msg` /
    /// `assert_vir_error_msg` — i.e. as ERROR outcomes carrying the label
    /// text — while unlabeled failures are plain counterexample outcomes
    /// (`assert_one_fails`/`assert_fails`).
    ///
    /// DELIBERATE VERDICT-TAXONOMY DECISION (flagged, not hidden): a
    /// counterexample against a USER-LABELED obligation is reported here as
    /// `VerifyResult::Error` with the label text, mirroring the upstream
    /// channel. This is reject-only/fail-closed — it can never produce
    /// `Verified`, and `Unknown` is never touched (no fabricated failure
    /// text for an undecided obligation) — and it is strictly opt-in: an
    /// obligation only carries a label when the user wrote one, so every
    /// unlabeled program's verdict is byte-for-byte unchanged.
    ///
    /// Ambiguity guard: several obligations can share a reported base name
    /// (every `ensures` clause is named "postcondition"). The mapping fires
    /// only when EVERY obligation with the failing base name carries the
    /// IDENTICAL label, so a failure that might belong to an unlabeled
    /// sibling clause keeps its counterexample verdict (upstream
    /// `test_ret`/`test_requires3` behavior: the failing clause is the
    /// unlabeled one). This can MISS a note when a labeled and an unlabeled
    /// same-named clause both exist and the labeled one fails — a documented,
    /// fail-toward-counterexample incompleteness, never a fabricated note.
    fn apply_proof_note_verdict(&self, result: VerifyResult) -> VerifyResult {
        let VerifyResult::Counterexample {
            obligation_name, ..
        } = &result
        else {
            return result;
        };
        // Derived obligations ("postcondition: possible addition overflow in
        // '…'") share the base name before the first ':'.
        let base = obligation_name
            .split(':')
            .next()
            .unwrap_or(obligation_name)
            .trim();
        // Only hard assertion-class obligations participate: soft
        // (`Recommends`) or assumption-class obligations must never be
        // upgraded to the error channel.
        let matching: Vec<_> = self
            .obligations
            .iter()
            .filter(|obligation| {
                obligation.name == base && matches!(obligation.kind, super::ObligationKind::Assert)
            })
            .collect();
        let Some(first) = matching.first() else {
            return result;
        };
        let Some(label) = first.proof_note.as_ref() else {
            return result;
        };
        if !matching
            .iter()
            .all(|obligation| obligation.proof_note.as_ref() == Some(label))
        {
            return result;
        }
        let message = if label.is_custom_err {
            label.text.clone()
        } else {
            format!(
                "{}\nnote: {}",
                proof_note_primary_failure_text(base),
                label.text
            )
        };
        VerifyResult::Error { message }
    }
}

/// The unchanged primary failure text a `proof_note` label annotates,
/// matching the upstream primary diagnostics ("assertion failed",
/// "precondition not satisfied", "postcondition not satisfied").
fn proof_note_primary_failure_text(base_name: &str) -> &'static str {
    if base_name == "postcondition" {
        "postcondition not satisfied"
    } else if base_name.starts_with("__call_requires_") {
        "precondition not satisfied"
    } else {
        "assertion failed"
    }
}
