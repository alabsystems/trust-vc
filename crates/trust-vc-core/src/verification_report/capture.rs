//! Internal capture helpers for verification reports.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::cell::RefCell;
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant};

use super::*;

#[derive(Default)]
struct ReportCollector {
    steps: Vec<StepDiagnostic>,
    #[cfg(feature = "proof-certificates")]
    proof: Option<ProofCertificate>,
}

#[derive(Clone)]
pub(crate) struct CaptureContext {
    collector: Arc<Mutex<ReportCollector>>,
    step_stack: Vec<usize>,
    suppression_depth: usize,
}

thread_local! {
    static ACTIVE_CAPTURE: RefCell<Option<CaptureContext>> = const { RefCell::new(None) };
}

pub(crate) fn capture_report(
    pipeline: Option<PipelineSummary>,
    f: impl FnOnce() -> VerifyResult,
) -> VerificationReport {
    let collector = Arc::new(Mutex::new(ReportCollector::default()));
    let capture = CaptureContext {
        collector: Arc::clone(&collector),
        step_stack: Vec::new(),
        suppression_depth: 0,
    };
    let start = Instant::now();
    let result = run_with_capture_context(Some(capture), f);
    let guard = lock_collector(&collector);
    let steps = guard.steps.clone();
    #[cfg(feature = "proof-certificates")]
    let proof = guard.proof.clone();
    drop(guard);
    let report = VerificationReport::from_parts(result, pipeline, steps, start.elapsed());
    #[cfg(feature = "proof-certificates")]
    let report = report.with_proof(proof);
    report
}

pub(crate) fn run_with_capture_context<T>(
    capture: Option<CaptureContext>,
    f: impl FnOnce() -> T,
) -> T {
    let prior = ACTIVE_CAPTURE.with(|slot| slot.replace(capture));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    ACTIVE_CAPTURE.with(|slot| {
        slot.replace(prior);
    });
    match result {
        Ok(value) => value,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

pub(crate) fn with_capture_suppressed<T>(f: impl FnOnce() -> T) -> T {
    ACTIVE_CAPTURE.with(|slot| {
        {
            let mut guard = slot.borrow_mut();
            if let Some(capture) = guard.as_mut() {
                capture.suppression_depth += 1;
            }
        }
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        {
            let mut guard = slot.borrow_mut();
            if let Some(capture) = guard.as_mut() {
                capture.suppression_depth = capture.suppression_depth.saturating_sub(1);
            }
        }
        match result {
            Ok(value) => value,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    })
}

pub(crate) fn begin_step(
    phase: VerificationPhase,
    label: impl Into<String>,
    location: Option<String>,
) -> Option<usize> {
    begin_step_with_condition(phase, label.into(), location, None)
}

fn begin_step_with_condition(
    phase: VerificationPhase,
    label: String,
    location: Option<String>,
    condition: Option<String>,
) -> Option<usize> {
    ACTIVE_CAPTURE.with(|slot| {
        let mut guard = slot.borrow_mut();
        let capture = guard.as_mut()?;
        if capture.suppression_depth > 0 {
            return None;
        }
        let mut collector = lock_collector(&capture.collector);
        let step_index = collector.steps.len();
        collector.steps.push(StepDiagnostic::pending_with_condition(
            phase, label, location, condition,
        ));
        capture.step_stack.push(step_index);
        Some(step_index)
    })
}

pub(crate) fn begin_obligation_step(
    phase: VerificationPhase,
    obligation: &PreparedObligation,
) -> Option<usize> {
    begin_step_with_condition(
        phase,
        obligation.name.clone(),
        obligation.location.clone(),
        Some(obligation.condition.clone()),
    )
}

pub(crate) fn end_step_with_assertion_result(
    step_index: Option<usize>,
    result: &crate::error::TrustVcResult<AssertionOutcome>,
    elapsed: Duration,
) {
    end_step(step_index, elapsed, |step| match result {
        Ok(AssertionOutcome::Verified) => {
            step.result = StepResultKind::Verified;
            step.unknown = None;
        }
        Ok(AssertionOutcome::Counterexample { .. }) => {
            step.result = StepResultKind::Counterexample;
            step.unknown = None;
        }
        Ok(AssertionOutcome::Unknown {
            reason, category, ..
        }) => {
            step.result = StepResultKind::Unknown;
            let category = category.unwrap_or_else(|| UnknownCategory::classify(reason));
            step.unknown = Some(unknown_from_category(category));
        }
        Ok(AssertionOutcome::Error { .. }) => {
            step.result = StepResultKind::Error;
            step.unknown = None;
        }
        Err(_) => {
            step.result = StepResultKind::Error;
            step.unknown = None;
        }
    });
}

pub(crate) fn end_step_with_verify_result(
    step_index: Option<usize>,
    result: &VerifyResult,
    elapsed: Duration,
) {
    end_step(step_index, elapsed, |step| {
        *step = apply_verify_result(step.clone(), result);
    });
}

pub(crate) fn end_step_verified(step_index: Option<usize>, elapsed: Duration) {
    end_step(step_index, elapsed, |step| {
        step.result = StepResultKind::Verified;
        step.unknown = None;
    });
}

pub(crate) fn end_step_skipped(step_index: Option<usize>, elapsed: Duration) {
    end_step(step_index, elapsed, |step| {
        step.result = StepResultKind::Skipped;
        step.unknown = None;
    });
}

pub(crate) fn record_solve_details(details: &SolveDetails, term_bytes: Option<usize>) {
    ACTIVE_CAPTURE.with(|slot| {
        let guard = slot.borrow();
        let Some(capture) = guard.as_ref() else {
            return;
        };
        if capture.suppression_depth > 0 {
            return;
        }
        let Some(step_index) = capture.step_stack.last().copied() else {
            return;
        };
        let mut collector = lock_collector(&capture.collector);
        if let Some(step) = collector.steps.get_mut(step_index) {
            step.solver = Some(SolverStats::from_solve_details(details, term_bytes));
        }
    });
}

pub(crate) fn record_demand_inline_recovery(inlined_functions: &[String], depth_used: usize) {
    ACTIVE_CAPTURE.with(|slot| {
        let guard = slot.borrow();
        let Some(capture) = guard.as_ref() else {
            return;
        };
        if capture.suppression_depth > 0 {
            return;
        }
        let Some(step_index) = capture.step_stack.last().copied() else {
            return;
        };
        let mut collector = lock_collector(&capture.collector);
        if let Some(step) = collector.steps.get_mut(step_index) {
            step.demand_inline_recovery = Some(DemandInlineRecovery {
                inlined_functions: inlined_functions.to_vec(),
                depth_used,
            });
        }
    });
}

pub(crate) fn record_used_assumptions(used_assumptions: &[String]) {
    ACTIVE_CAPTURE.with(|slot| {
        let guard = slot.borrow();
        let Some(capture) = guard.as_ref() else {
            return;
        };
        if capture.suppression_depth > 0 {
            return;
        }
        let Some(step_index) = capture.step_stack.last().copied() else {
            return;
        };
        let mut collector = lock_collector(&capture.collector);
        if let Some(step) = collector.steps.get_mut(step_index) {
            step.used_assumptions = used_assumptions.to_vec();
        }
    });
}

pub(crate) fn step_from_verify_result(
    phase: VerificationPhase,
    label: impl Into<String>,
    location: Option<String>,
    elapsed: Duration,
    result: &VerifyResult,
) -> StepDiagnostic {
    StepDiagnostic::from_verify_result(phase, label.into(), location, elapsed, result)
}

fn end_step(step_index: Option<usize>, elapsed: Duration, apply: impl FnOnce(&mut StepDiagnostic)) {
    let Some(expected_index) = step_index else {
        return;
    };
    ACTIVE_CAPTURE.with(|slot| {
        let mut guard = slot.borrow_mut();
        let Some(capture) = guard.as_mut() else {
            return;
        };
        if capture.step_stack.pop() != Some(expected_index) {
            return;
        }
        let mut collector = lock_collector(&capture.collector);
        if let Some(step) = collector.steps.get_mut(expected_index) {
            step.elapsed = elapsed;
            apply(step);
        }
    });
}

fn lock_collector(collector: &Arc<Mutex<ReportCollector>>) -> MutexGuard<'_, ReportCollector> {
    match collector.lock() {
        Ok(guard) => guard,
        Err(poisoned) => poisoned.into_inner(),
    }
}

/// True iff a STRICT-checked refutation of `obligation`'s own negated goal has
/// been recorded for the step currently open.
///
/// "Strict-checked" is [`ProofCertificate::strict_verified`], which requires
/// the certificate's premises to be the posed query: a refutation with a
/// premise trust-vc never asserted is no determinism guarantee about the
/// obligation, so the confirmation re-solve runs for it.
///
/// Callers use this to skip the confirmation re-solve (#2706 slice 3): a strict
/// proof certificate is a stronger determinism guarantee than running the same
/// query a second time. That argument holds only for the assertion the
/// certificate actually refutes, so the identity is a parameter (#2654).
///
/// This used to take no argument and, when the open step had no certificate,
/// fall through to `collector.proof` — the unit-level "last proof produced"
/// slot, which routinely belongs to a DIFFERENT obligation. Under that fallback
/// assertion `A` could skip its confirmation check because assertion `B` had
/// produced a strict proof, which is not a determinism guarantee about `A` at
/// all. There is no correct unit-level answer to a per-assertion question, so
/// the fallback is gone: no per-assertion certificate means `false`, and the
/// confirmation re-solve runs. That is the fail-closed direction — it can only
/// add checking.
#[cfg(feature = "proof-certificates")]
pub(crate) fn current_proof_is_strict(obligation: &str) -> bool {
    ACTIVE_CAPTURE.with(|slot| {
        let guard = slot.borrow();
        let Some(capture) = guard.as_ref() else {
            return false;
        };
        let collector = lock_collector(&capture.collector);
        let Some(step_index) = capture.step_stack.last().copied() else {
            return false;
        };
        let Some(step) = collector.steps.get(step_index) else {
            return false;
        };
        step.proof()
            .is_some_and(|proof| proof.strict_verified() && proof.refutes_obligation(obligation))
    })
}

/// Record the solver's UNSAT refutation of `refuted_obligation`'s negated goal.
///
/// `refuted_obligation` is the `PreparedObligation::name` of the goal that was
/// actually negated and asserted into the scope the solver just decided UNSAT.
/// It comes from the solve site, which holds the obligation itself.
///
/// # Identity binding (#2654)
///
/// The certificate is attached to the open report step ONLY when that step's
/// label is `refuted_obligation`. That equality is what makes the attachment a
/// claim about the step's own goal.
///
/// The check is not cosmetic. Several paths issue more than one solver query
/// under a single obligation step, and this function used to attach whatever
/// arrived last:
///
/// * `verification::split::try_verify_quantified_conjunction_split` discharges
///   `forall x. (C1 AND ... AND Cn)` as `n` separate `forall x. Ck` queries
///   under the parent's step. Each sub-query names itself
///   `"<parent> [forall conjunct k of n]"`, so the last one used to overwrite
///   the parent step's certificate with a refutation of `Ck` alone — measured
///   in `tests/proof_certificate_assertion_identity.rs`.
/// * `try_localize_failure` splits the same way on the counterexample path.
///
/// A mismatched artifact is DROPPED rather than attached. That leaves the step
/// with no certificate, which every downstream consumer already treats as "no
/// replayable evidence" and fails closed on under a policy that requires one. It
/// is never replaced by a weaker or synthesized certificate.
///
/// A mismatch does not disturb a certificate already attached for this step's
/// own goal: an Alethe refutation is self-contained (it carries its own `assume`
/// steps), so a genuine refutation of `NOT goal` stays a genuine refutation of
/// `NOT goal` no matter what query runs afterwards. Dropping it would lose real
/// evidence for no soundness gain.
///
/// # Premise binding
///
/// Identity says which query was refuted; it does not say the certificate's
/// `assume` steps ARE that query. `evidence` is computed at the solve site,
/// which still holds the query trust-vc posed (see
/// `kernel_bridge::certify_last_refutation`): it binds the premises and runs
/// the kernel. It is evaluated only when a report is capturing, and before the
/// certificate is attached anywhere, so neither a step nor `collector.proof`
/// ever carries a strict or kernel claim for a certificate whose premises are
/// foreign to the query.
///
/// `collector.proof` still receives every artifact (it is the unit-level
/// "last proof produced" slot, used for diagnostics and for the single-assertion
/// fallback in `trust-vc-trust-engine`). It now carries its own identity, so
/// that fallback can check the binding instead of inferring it from cardinality.
#[cfg(feature = "proof-certificates")]
pub(crate) fn record_proof_artifact(
    artifact: &ay_dpll::api::UnsatProofArtifact,
    evidence: impl FnOnce() -> super::kernel_bridge::CertificateEvidence,
    refuted_obligation: &str,
) {
    ACTIVE_CAPTURE.with(|slot| {
        let guard = slot.borrow();
        let Some(capture) = guard.as_ref() else {
            return;
        };
        if capture.suppression_depth > 0 {
            return;
        }
        let cert = ProofCertificate::from_artifact(artifact, refuted_obligation)
            .with_evidence(&evidence());

        let mut collector = lock_collector(&capture.collector);
        if let Some(step_index) = capture.step_stack.last().copied() {
            if let Some(step) = collector.steps.get_mut(step_index) {
                if cert.refutes_obligation(&step.label) {
                    step.proof = Some(cert.clone());
                } else {
                    // This refutation is of a DIFFERENT goal than the one this
                    // step reports (a sub-query of a split, typically). It is a
                    // real refutation, but not of this assertion, so it may not
                    // stand as this assertion's certificate.
                    tracing::debug!(
                        step_label = %step.label,
                        refuted_obligation = %refuted_obligation,
                        existing_proof = step.proof.is_some(),
                        "dropping proof certificate: it refutes a different goal \
                         than the step it would be attached to (#2654)"
                    );
                }
            }
        }
        collector.proof = Some(cert);
    });
}
