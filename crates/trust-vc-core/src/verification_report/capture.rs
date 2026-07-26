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

/// Returns `true` when the current step's proof certificate passed strict
/// validation.  Used by the confirmation-skip optimisation (Slice 3 of #2706):
/// a strict UNSAT proof is a stronger guarantee than a second solver run, so
/// we can skip the collection-confirmation re-check.
#[cfg(feature = "proof-certificates")]
pub(crate) fn current_proof_is_strict() -> bool {
    ACTIVE_CAPTURE.with(|slot| {
        let guard = slot.borrow();
        let Some(capture) = guard.as_ref() else {
            return false;
        };
        let collector = lock_collector(&capture.collector);
        if let Some(step_index) = capture.step_stack.last().copied() {
            if let Some(step) = collector.steps.get(step_index) {
                if let Some(proof) = step.proof() {
                    return proof.strict_verified();
                }
            }
        }

        collector
            .proof
            .as_ref()
            .is_some_and(|p| p.strict_verified())
    })
}

#[cfg(feature = "proof-certificates")]
pub(crate) fn record_proof_artifact(
    artifact: &ay_dpll::api::UnsatProofArtifact,
    proof: Option<&ay_core::Proof>,
) {
    ACTIVE_CAPTURE.with(|slot| {
        let guard = slot.borrow();
        let Some(capture) = guard.as_ref() else {
            return;
        };
        if capture.suppression_depth > 0 {
            return;
        }
        let mut cert = ProofCertificate::from_artifact(artifact);

        // Run the trust-vc-kernel independent checker if the raw proof is available.
        if let Some(ay_proof) = proof {
            let kernel_ok = super::kernel_bridge::verify_proof_with_kernel(ay_proof, None);
            cert = cert.with_kernel_verified(kernel_ok);
        }

        let mut collector = lock_collector(&capture.collector);
        if let Some(step_index) = capture.step_stack.last().copied() {
            if let Some(step) = collector.steps.get_mut(step_index) {
                step.proof = Some(cert.clone());
            }
        }
        collector.proof = Some(cert);
    });
}
