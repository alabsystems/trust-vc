//! Solver-thread timeout handoff for assertion verification.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::panic::AssertUnwindSafe;
use std::time::Duration;

use super::outcome::{AssertionOutcome, SolverUnknownDetail};
use super::panic::catch_ay_panic_to_unknown;
use super::test_hooks::{bump_shared_bv_reuse_attempt_count, force_bv_timeout_enabled};
#[cfg(not(test))]
use super::timeout::reserve_solver_thread_slot;
use super::timeout::{effective_bv_timeout, far_out_watchdog_timeout, BV_HARD_TIMEOUT};
use super::unknown_category::UnknownCategory;
use crate::encoder::AYEncoder;
use crate::error::TrustVcResult;
use ay_dpll::UnknownReason;

pub(super) fn format_forced_timeout_reason(assertion_name: &str) -> String {
    format_timeout_reason(
        assertion_name,
        BV_HARD_TIMEOUT,
        "BV solver timeout enforcement, #1605",
    )
}

fn format_timeout_duration(timeout: Duration) -> String {
    if timeout.subsec_millis() == 0 {
        format!("{}s", timeout.as_secs())
    } else {
        format!("{}ms", timeout.as_millis())
    }
}

fn format_timeout_reason(assertion_name: &str, timeout: Duration, timeout_label: &str) -> String {
    format!(
        "Solver timed out after {} for '{}' ({})",
        format_timeout_duration(timeout),
        assertion_name,
        timeout_label
    )
}

pub(super) fn forced_timeout_result(assertion_name: &str) -> AssertionOutcome {
    AssertionOutcome::unknown(
        format_forced_timeout_reason(assertion_name),
        Some(UnknownCategory::Timeout),
    )
}

fn timeout_result(
    assertion_name: &str,
    timeout: Duration,
    timeout_label: &str,
) -> AssertionOutcome {
    AssertionOutcome::unknown(
        format_timeout_reason(assertion_name, timeout, timeout_label),
        Some(UnknownCategory::Timeout),
    )
}

fn is_watchdog_interrupted_timeout(outcome: &AssertionOutcome, timed_out: bool) -> bool {
    timed_out
        && matches!(
            outcome,
            AssertionOutcome::Unknown {
                detail: Some(SolverUnknownDetail::AY(UnknownReason::Interrupted)),
                ..
            }
        )
}

fn map_watchdog_interrupted_to_timeout(
    outcome: AssertionOutcome,
    timed_out: bool,
    assertion_name: &str,
    timeout: Duration,
    timeout_label: &str,
) -> AssertionOutcome {
    if is_watchdog_interrupted_timeout(&outcome, timed_out) {
        timeout_result(assertion_name, timeout, timeout_label)
    } else {
        outcome
    }
}

/// Watchdog label for the far-out hang-backstop profile (see
/// `deterministic_budget_governed` / `timeout::far_out_watchdog_timeout`).
const FAR_OUT_TIMEOUT_LABEL: &str =
    "far-out hang backstop; deterministic solver budgets govern, ay 62695cfe04";

/// Is this obligation's solve governed by ay's DETERMINISTIC budgets rather
/// than the wall clock (#quantifier-determinism, ay 62695cfe04)?
///
/// True for solves that enter ay's quantified pipeline (quantified assertions
/// already in the solver, a quantified goal, or a collection-referencing goal
/// whose encoding lazily emits quantified axioms) and for explicit
/// `by(nonlinear_arith)` obligations (ay's NIA/SOS lane — count-bounded
/// search, not exponential ground bit-blasting). For these, the external
/// watchdog must be a far-out hang backstop sitting beyond ay's own
/// (backstopped — the opt-in `AYEncoder::with_limits` installs, since ay
/// 6226726f3 left it OFF by default) deadline: a tight wall-clock kill here re-creates the
/// machine-load Verified<->Unknown flip the deterministic budgets exist to
/// prevent (the calc.rs seq-chain flake; nonlinear.rs test5 under load).
///
/// Deliberate overapproximation, and safe in exactly one direction: a `true`
/// here only RAISES the hang-protection deadline (ay's internal deadline
/// still terminates the solve); verdicts can only change by letting
/// deterministic work complete. Ground/BV obligations keep the tight
/// `BV_HARD_TIMEOUT` and their prompt retry ladder.
fn deterministic_budget_governed(
    encoder: &AYEncoder,
    assertion: &crate::prepared_context::PreparedObligation,
) -> bool {
    matches!(
        assertion.solver_mode,
        Some(crate::vc::SolverMode::NonlinearArith)
    ) || assertion.expr.contains_quantifier()
        || assertion.expr.references_collection()
        || encoder.has_quantified_assertions()
}

/// Watchdog parameters for one timeout-wrapped attempt.
struct WatchdogBudget {
    timeout: Duration,
    label: &'static str,
}

/// Pick the watchdog duration + reason label for one timeout-wrapped attempt.
///
/// `base` is the tight-profile duration the caller would historically have
/// used (`effective_bv_timeout` or its extended 2x variant). Obligations whose
/// solve is governed by deterministic solver budgets get the far-out backstop
/// instead (never smaller than `base`).
fn watchdog_budget(
    encoder: &AYEncoder,
    assertion: &crate::prepared_context::PreparedObligation,
    rlimit_ms: Option<u64>,
    base: Duration,
    base_label: &'static str,
) -> WatchdogBudget {
    if deterministic_budget_governed(encoder, assertion) {
        WatchdogBudget {
            timeout: far_out_watchdog_timeout(rlimit_ms).max(base),
            label: FAR_OUT_TIMEOUT_LABEL,
        }
    } else {
        WatchdogBudget {
            timeout: base,
            label: base_label,
        }
    }
}

pub(super) struct WatchdogResult<T> {
    pub(super) result: std::thread::Result<T>,
    pub(super) timed_out: bool,
}

pub(super) fn run_with_timeout_watchdog<T>(
    interrupt: std::sync::Arc<std::sync::atomic::AtomicBool>,
    timeout: Duration,
    _force_scope_pop_failure: bool,
    f: impl FnOnce() -> T,
) -> WatchdogResult<T> {
    let (done_tx, done_rx) = std::sync::mpsc::channel::<()>();
    let timed_out = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let watchdog_timed_out = std::sync::Arc::clone(&timed_out);
    let watchdog = std::thread::spawn(move || {
        if matches!(
            done_rx.recv_timeout(timeout),
            Err(std::sync::mpsc::RecvTimeoutError::Timeout)
        ) {
            watchdog_timed_out.store(true, std::sync::atomic::Ordering::Relaxed);
            interrupt.store(true, std::sync::atomic::Ordering::Relaxed);
        }
    });

    #[cfg(test)]
    if _force_scope_pop_failure {
        super::test_hooks::FORCE_SCOPE_POP_FAILURE_ONCE.with(|flag| flag.set(true));
    }

    #[cfg(debug_assertions)]
    let prior_timeout_context = super::timeout::IN_TIMEOUT_CONTEXT.with(|flag| {
        let prior = flag.get();
        flag.set(true);
        prior
    });

    let result = std::panic::catch_unwind(AssertUnwindSafe(f));

    #[cfg(debug_assertions)]
    super::timeout::IN_TIMEOUT_CONTEXT.with(|flag| flag.set(prior_timeout_context));

    #[cfg(test)]
    if _force_scope_pop_failure {
        super::test_hooks::FORCE_SCOPE_POP_FAILURE_ONCE.with(|flag| flag.set(false));
    }

    let _ = done_tx.send(());
    let _ = watchdog.join();
    WatchdogResult {
        result,
        timed_out: timed_out.load(std::sync::atomic::Ordering::Relaxed),
    }
}

fn map_solver_panic(
    panic_payload: Box<dyn std::any::Any + Send>,
    assertion_name: &str,
    disconnect_suffix: &str,
) -> TrustVcResult<AssertionOutcome> {
    match std::panic::catch_unwind(AssertUnwindSafe(|| {
        catch_ay_panic_to_unknown(panic_payload, assertion_name)
    })) {
        Ok(result) => result,
        Err(_) => Ok(AssertionOutcome::unknown(
            format!(
                "Solver thread panicked (non-ay) for '{}'{}",
                assertion_name, disconnect_suffix,
            ),
            Some(UnknownCategory::ThreadPanic),
        )),
    }
}

/// Core timeout wrapper parameterized by the tight-profile base duration.
///
/// Runs the solver on the current thread and arms a watchdog thread that
/// flips the solver's interrupt handle when the deadline expires. This keeps
/// timeout enforcement compatible with ay-dpll versions whose `Solver`
/// contains non-`Send` internals while preserving the existing timeout
/// contract for BV checks.
///
/// Deterministic-budget-governed obligations (see
/// `deterministic_budget_governed`) get the far-out watchdog instead of
/// `base_timeout`: ay's own (nominal, possibly quantified-entry-backstopped —
/// the opt-in `AYEncoder::with_limits` installs) deadline governs termination
/// and the watchdog is pure hang protection.
/// The solver-internal nominal deadline is deliberately NOT raised —
/// ay keeps ground-phase deadlines at the exact nominal by design
/// ("caller retry ladders stay prompt", ay 62695cfe04), and a caller-side
/// raise was measured to only slow non-converging solves 4x without
/// flipping any verdict (calc.rs line93 churns >300s on this machine).
fn verify_with_timeout_inner(
    mut encoder: AYEncoder,
    assertion: &crate::prepared_context::PreparedObligation,
    rlimit_ms: Option<u64>,
    base_timeout: Duration,
    base_label: &'static str,
    disconnect_suffix: &str,
) -> TrustVcResult<AssertionOutcome> {
    let budget = watchdog_budget(&encoder, assertion, rlimit_ms, base_timeout, base_label);
    let (timeout, timeout_label) = (budget.timeout, budget.label);
    #[cfg(not(test))]
    let _guard = reserve_solver_thread_slot();
    #[cfg(test)]
    let _guard = super::timeout::reserve_solver_thread_slot_for_current_work();
    let interrupt = encoder.interrupt_handle();
    #[cfg_attr(not(test), allow(unused_variables))]
    let force_scope_pop_failure = super::test_hooks::take_forced_scope_pop_failure();

    let assertion_owned = assertion.clone();
    let watchdog_result =
        run_with_timeout_watchdog(interrupt, timeout, force_scope_pop_failure, || {
            let _guard = _guard;
            encoder.verify_assertion_typed(&assertion_owned)
        });

    match watchdog_result.result {
        Ok(inner_result) => inner_result.map(|outcome| {
            map_watchdog_interrupted_to_timeout(
                outcome,
                watchdog_result.timed_out,
                &assertion_owned.name,
                timeout,
                timeout_label,
            )
        }),
        Err(panic_info) => map_solver_panic(panic_info, &assertion_owned.name, disconnect_suffix),
    }
}

/// Typed assertion timeout wrapper — uses effective timeout from `rlimit_ms`.
///
/// The `PreparedObligation` carries its `TrustVcExpr` directly, so the
/// spawned thread doesn't need `PREPARED_CONDITIONS` installed. This
/// eliminates the thread-crossing dance. Part of #2219.
///
/// When `rlimit_ms` is `Some(ms)`, the hard timeout is set to `ms`
/// (may be lower or higher than `BV_HARD_TIMEOUT`). Pass `None` for
/// default behavior. Part of #2577.
pub(super) fn verify_assertion_with_timeout_typed(
    encoder: AYEncoder,
    assertion: &crate::prepared_context::PreparedObligation,
    rlimit_ms: Option<u64>,
) -> TrustVcResult<AssertionOutcome> {
    verify_with_timeout_inner(
        encoder,
        assertion,
        rlimit_ms,
        effective_bv_timeout(rlimit_ms),
        "BV solver timeout enforcement, #1605",
        "",
    )
}

/// Extended-timeout variant for recovering marginal timeouts caused by
/// ay-dpll non-determinism (#2273).
///
/// When `rlimit_ms` is `None` (default), uses `2 * BV_HARD_TIMEOUT` to give
/// the solver more time. When `rlimit_ms` is explicitly set, does NOT double
/// — the user's stated budget is the ceiling. Part of #2313, #2577.
pub(super) fn verify_assertion_with_timeout_typed_extended(
    encoder: AYEncoder,
    assertion: &crate::prepared_context::PreparedObligation,
    rlimit_ms: Option<u64>,
) -> TrustVcResult<AssertionOutcome> {
    let base = match rlimit_ms {
        Some(_) => effective_bv_timeout(rlimit_ms),
        None => BV_HARD_TIMEOUT * 2,
    };
    verify_with_timeout_inner(
        encoder,
        assertion,
        rlimit_ms,
        base,
        "extended-timeout retry, #2313",
        " during extended retry",
    )
}

/// Result of a reusable timeout-wrapped assertion check.
///
/// On non-timeout outcomes, the encoder is returned so the caller can reuse
/// it for subsequent assertions (shared solver context via push/pop). On
/// timeout or panic, the encoder is consumed by the solver thread and cannot
/// be recovered.
///
/// Part of #2496.
#[allow(clippy::large_enum_variant)]
pub(in crate::encoder) enum ReuseAttempt {
    /// Assertion completed (Verified, Counterexample, or Unknown non-timeout).
    /// The encoder is returned for reuse.
    Completed {
        encoder: AYEncoder,
        outcome: AssertionOutcome,
    },
    /// Assertion completed, but a solver scope failure made the encoder unsafe
    /// to reuse for subsequent assertions. Part of #2552.
    NonReusable { outcome: AssertionOutcome },
    /// Solver timed out. The encoder is consumed and cannot be reused.
    TimedOut,
    /// Solver thread panicked. The encoder is in inconsistent state.
    Panicked { outcome: AssertionOutcome },
}

/// Reusable timeout wrapper that returns the encoder on non-timeout outcomes.
///
/// Unlike `verify_with_timeout_inner`, this sends the encoder back through
/// the channel alongside the result so the caller can reuse it for the next
/// assertion. On timeout or panic, the encoder is lost (consumed by the
/// solver thread).
///
/// The caller must call `encoder.state.ground_pool.reset_flush_state()` before
/// each invocation to ensure ground axioms are re-flushed after push/pop
/// retracts solver assertions from the previous assertion check.
///
/// Part of #2496, #2577.
pub(in crate::encoder) fn verify_assertion_with_timeout_reuse(
    mut encoder: AYEncoder,
    assertion: &crate::prepared_context::PreparedObligation,
    rlimit_ms: Option<u64>,
) -> TrustVcResult<ReuseAttempt> {
    bump_shared_bv_reuse_attempt_count();
    if force_bv_timeout_enabled() {
        return Ok(ReuseAttempt::TimedOut);
    }

    #[cfg(not(test))]
    let _guard = reserve_solver_thread_slot();
    #[cfg(test)]
    let _guard = super::timeout::reserve_solver_thread_slot_for_current_work();
    let interrupt = encoder.interrupt_handle();
    #[cfg_attr(not(test), allow(unused_variables))]
    let force_scope_pop_failure = super::test_hooks::take_forced_scope_pop_failure();

    // Shared encoder: same watchdog-profile selection as the per-assertion
    // path (the tight kill would otherwise re-create the load-flip hazard for
    // any deterministic-budget-governed obligation that lands here).
    let budget = watchdog_budget(
        &encoder,
        assertion,
        rlimit_ms,
        effective_bv_timeout(rlimit_ms),
        "BV solver timeout enforcement, #1605",
    );
    let assertion_owned = assertion.clone();
    let watchdog_result =
        run_with_timeout_watchdog(interrupt, budget.timeout, force_scope_pop_failure, || {
            let _guard = _guard;
            encoder.verify_assertion_typed(&assertion_owned)
        });

    match watchdog_result.result {
        Ok(inner_result) => {
            let outcome = inner_result?;
            if is_watchdog_interrupted_timeout(&outcome, watchdog_result.timed_out) {
                return Ok(ReuseAttempt::TimedOut);
            }
            if encoder.state.reusable_after_scope && encoder.state.solver_panic.is_none() {
                Ok(ReuseAttempt::Completed { encoder, outcome })
            } else {
                Ok(ReuseAttempt::NonReusable { outcome })
            }
        }
        Err(panic_info) => Ok(ReuseAttempt::Panicked {
            outcome: map_solver_panic(panic_info, &assertion_owned.name, " (shared fast path)")?,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interrupted_unknown() -> AssertionOutcome {
        AssertionOutcome::unknown_with_detail(
            "Solver returned unknown (interrupted) for 'left_boundary'",
            Some(UnknownCategory::SolverUnknown),
            Some(SolverUnknownDetail::AY(UnknownReason::Interrupted)),
        )
    }

    #[test]
    fn test_watchdog_interrupted_maps_to_timeout() {
        let outcome = map_watchdog_interrupted_to_timeout(
            interrupted_unknown(),
            true,
            "left_boundary",
            Duration::from_millis(250),
            "test watchdog",
        );

        match outcome {
            AssertionOutcome::Unknown {
                reason,
                category,
                detail,
            } => {
                assert_eq!(category, Some(UnknownCategory::Timeout));
                assert_eq!(detail, None);
                assert!(
                    reason.contains("timed out after 250ms"),
                    "timeout reason should include watchdog duration: {reason}"
                );
                assert!(
                    reason.contains("test watchdog"),
                    "timeout reason should include watchdog label: {reason}"
                );
            }
            other => panic!("expected timeout unknown, got {other:?}"),
        }
    }

    #[test]
    fn test_external_interrupted_stays_solver_unknown() {
        let outcome = map_watchdog_interrupted_to_timeout(
            interrupted_unknown(),
            false,
            "left_boundary",
            Duration::from_millis(250),
            "test watchdog",
        );

        match outcome {
            AssertionOutcome::Unknown {
                reason,
                category,
                detail,
            } => {
                assert_eq!(category, Some(UnknownCategory::SolverUnknown));
                assert_eq!(
                    detail,
                    Some(SolverUnknownDetail::AY(UnknownReason::Interrupted))
                );
                assert!(
                    reason.contains("interrupted"),
                    "non-watchdog interrupt should retain original reason: {reason}"
                );
            }
            other => panic!("expected interrupted unknown, got {other:?}"),
        }
    }
}
