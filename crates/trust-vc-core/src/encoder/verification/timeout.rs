//! Solver-thread capacity and timeout control.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

/// Hard timeout for BV solver queries that bypass ay-dpll's internal timeout.
///
/// ay-dpll's BV solver calls `SatSolver::solve()` (non-interruptible) instead of
/// `solve_interruptible()`, so the solver-level timeout set via `with_limits()` is
/// ignored during BV SAT solving (#1605, #1682). This thread-based timeout ensures
/// verification always terminates by running `check_sat()` in a separate thread
/// and joining with a deadline.
///
/// Set to 10s rather than 30s to prevent timeout accumulation across the full test
/// suite (#1682). With ~870 solver invocations across ~1,045 individual assertions
/// in the test suite, a 30s timeout causes worst-case accumulation far exceeding
/// the 600s cargo test timeout. 10s is sufficient for all solvable BV problems
/// (most complete in <1s; the hardest — modulo identities — need ~5-8s). Problems
/// that don't finish in 10s are stuck in exponential BV DPLL search.
pub(in crate::encoder) const BV_HARD_TIMEOUT: Duration = Duration::from_secs(10);

/// Default nominal solver budget handed to ay via `with_limits()` when the
/// verification context carries no explicit `rlimit_ms`. Single source of
/// truth shared by encoder setup (`setup.rs`) and the far-out watchdog
/// derivation below — the watchdog must never be derived from a different
/// nominal than the one the solver was actually configured with.
pub(in crate::encoder) const DEFAULT_SOLVER_NOMINAL_TIMEOUT_MS: u64 = 30_000;

/// Scale factor ay applies to the REMAINING nominal budget at the quantified
/// entry (`install_quantifier_deadline_backstop`, ay 62695cfe04): the solver's
/// own deadline is extended by `remaining × (FACTOR - 1)`, capped at
/// `+MAX_EXTRA`. Mirrored here so the external watchdog for deterministic-
/// budget-governed solves sits *beyond* ay's own worst-case deadline.
const AY_QUANTIFIED_BACKSTOP_FACTOR: u32 = 4;

/// Absolute cap on ay's backstop extension (mirror of
/// `QUANTIFIED_BACKSTOP_MAX_EXTRA` in ay's
/// `install_quantifier_deadline_backstop`, ay 62695cfe04).
const AY_QUANTIFIED_BACKSTOP_MAX_EXTRA: Duration = Duration::from_secs(180);

/// Grace period added on top of ay's worst-case internal deadline so the
/// watchdog only fires when ay has genuinely failed to honor its own budget
/// (a hang), never in a race with ay's own truthfully-attributed stop.
const FAR_OUT_WATCHDOG_GRACE: Duration = Duration::from_secs(10);

/// Far-out hang-protection watchdog for obligations whose solve is governed
/// by ay's DETERMINISTIC budgets (#quantifier-determinism, ay 62695cfe04).
///
/// The tight `BV_HARD_TIMEOUT` exists for ground bit-blast SAT searches that
/// historically ignored ay's solver-level timeout (#1605/#1682) and for suite
/// latency: a ground BV problem that hasn't finished in 10s is stuck in
/// exponential DPLL search. Quantified / collection-axiom / nonlinear-hinted
/// obligations are different: since ay 62695cfe04 their termination is
/// PRIMARILY the deterministic instantiation/round/count budgets (identical
/// work on any machine), with ay's own wall clock relaxed to a far-out
/// backstop (`nominal + min(3 × nominal, 180s)`) precisely so machine load
/// cannot truncate a converging proof mid-pipeline. A flat 10s external
/// watchdog re-introduced the wall clock as the PRIMARY truncation and made
/// ported-gate verdicts flip with CPU load (the calc.rs seq-chain flake, and
/// the nonlinear.rs test5 flip under a loaded suite run). For these
/// obligations the external watchdog is therefore derived from the nominal
/// solver budget the encoder actually configured (`with_limits`, see
/// `DEFAULT_SOLVER_NOMINAL_TIMEOUT_MS`), mirrored through ay's own backstop
/// formula, plus a grace period: it can only fire when ay has failed to honor
/// its own deadline — true hang protection, never a verdict boundary.
///
/// With the defaults this is 30s + 90s + 10s = 130s. It scales with an
/// explicit `rlimit_ms` exactly like ay's own backstop scales with the
/// caller's `set_timeout`.
pub(in crate::encoder) fn far_out_watchdog_timeout(rlimit_ms: Option<u64>) -> Duration {
    far_out_nominal_timeout(rlimit_ms) + FAR_OUT_WATCHDOG_GRACE
}

/// The backstopped SOLVER-INTERNAL deadline ay's
/// `install_quantifier_deadline_backstop` (ay 62695cfe04) can extend a
/// deterministic-budget-governed solve to: `nominal + min(3 × nominal, 180s)`
/// (120s with the defaults). The external watchdog adds
/// `FAR_OUT_WATCHDOG_GRACE` on top so it can only fire when ay has failed to
/// honor its own (possibly extended) deadline.
fn far_out_nominal_timeout(rlimit_ms: Option<u64>) -> Duration {
    let nominal = Duration::from_millis(rlimit_ms.unwrap_or(DEFAULT_SOLVER_NOMINAL_TIMEOUT_MS));
    let backstop_extra = nominal
        .saturating_mul(AY_QUANTIFIED_BACKSTOP_FACTOR.saturating_sub(1))
        .min(AY_QUANTIFIED_BACKSTOP_MAX_EXTRA);
    nominal + backstop_extra
}

/// Compute the effective BV hard timeout, respecting an optional per-function
/// `rlimit_ms` override from `VerificationContext::set_rlimit()`.
///
/// When `rlimit_ms` is set, the effective timeout is the explicit value —
/// it may be lower *or* higher than `BV_HARD_TIMEOUT`. This allows
/// negative-verification tests to reduce the timeout below the default 10s
/// (preventing timeout accumulation in the retry cascade), and NIA-heavy
/// assertions to raise it above 10s when the solver needs more time.
/// Part of #2577.
pub(in crate::encoder) fn effective_bv_timeout(rlimit_ms: Option<u64>) -> Duration {
    match rlimit_ms {
        Some(ms) => Duration::from_millis(ms),
        None => BV_HARD_TIMEOUT,
    }
}

/// Default maximum concurrent solver threads when `TRUST_VC_MAX_SOLVER_THREADS`
/// is not set. Computed as `available_parallelism() / 2` to avoid memory
/// pressure, with a minimum of 2. This matches the acceptance criterion in
/// #2647: "default: num_cores / 2". See also #1682, #1703, #1704.
fn default_max_solver_threads() -> usize {
    std::thread::available_parallelism()
        .map(|n| (n.get() / 2).max(2))
        .unwrap_or(2)
}

/// Returns the maximum number of concurrent solver threads.
///
/// Reads `TRUST_VC_MAX_SOLVER_THREADS` from the environment on first call and
/// caches the result for the process lifetime. Defaults to `num_cores / 2`
/// (minimum 2).
///
/// This controls both the solver-thread limiter and the batch parallelism
/// level in `verify_batch_parallel`. Part of #2647.
pub(in crate::encoder) fn max_solver_threads() -> usize {
    static CACHED: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| {
        std::env::var("TRUST_VC_MAX_SOLVER_THREADS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or_else(default_max_solver_threads)
    })
}

/// Global count of live (spawned but not yet finished) solver threads.
pub(in crate::encoder) static LIVE_SOLVER_THREADS: AtomicUsize = AtomicUsize::new(0);

/// Reserves a solver thread slot by waiting for capacity and atomically
/// incrementing the counter. Returns a guard that decrements the counter
/// on drop. The increment happens on the calling thread (before
/// `thread::spawn`) and uses CAS to avoid over-reserving under contention.
/// Fixes #1710.
///
/// Waits up to `BV_HARD_TIMEOUT` for a slot to free up; if none does,
/// proceeds anyway (best-effort) to avoid deadlock.
pub(in crate::encoder) fn reserve_solver_thread_slot() -> SolverThreadGuard {
    let deadline = std::time::Instant::now() + BV_HARD_TIMEOUT;
    loop {
        let current = LIVE_SOLVER_THREADS.load(Ordering::Acquire);
        if current < max_solver_threads() {
            if LIVE_SOLVER_THREADS
                .compare_exchange_weak(current, current + 1, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                return SolverThreadGuard;
            }
            continue;
        }
        if std::time::Instant::now() >= deadline {
            break;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    // Best-effort fallback: preserve prior behavior of eventually progressing
    // even when slots stay saturated for a full timeout interval. Log the
    // oversubscription count for OOM diagnostics.
    let oversubscribed = LIVE_SOLVER_THREADS.fetch_add(1, Ordering::AcqRel);
    tracing::warn!(
        live_threads = oversubscribed + 1,
        max = max_solver_threads(),
        "Solver thread limiter bypassed — memory pressure risk"
    );
    SolverThreadGuard
}

/// RAII guard that decrements `LIVE_SOLVER_THREADS` on drop, even if the
/// thread panics. Without this, a panic in `verify_assertion` would leave
/// the counter permanently inflated, eventually deadlocking the limiter.
///
/// Created by `reserve_solver_thread_slot()`, which increments the counter
/// on the calling thread before returning this guard. The guard is then
/// moved into the spawned thread so the decrement happens when the thread
/// exits (or panics). Fixes #1710.
pub(in crate::encoder) struct SolverThreadGuard;

impl Drop for SolverThreadGuard {
    fn drop(&mut self) {
        LIVE_SOLVER_THREADS.fetch_sub(1, Ordering::AcqRel);
    }
}

// Thread-local flag: current thread is running within a timeout-protected
// solver context. `verify_assertion()` checks this via `debug_assert!` to
// catch direct calls that bypass timeout protection (#1705).
#[cfg(debug_assertions)]
thread_local! {
    pub(in crate::encoder) static IN_TIMEOUT_CONTEXT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier, Mutex};

    /// Mutex to serialize SolverThreadGuard tests against each other.
    /// With test-local counters (#1930), serialization prevents mutual
    /// capacity starvation (all guard tests contending for the 4 global
    /// slots simultaneously) rather than protecting counter observations.
    static GUARD_TEST_MUTEX: Mutex<()> = Mutex::new(());

    fn with_serialized_guard_test(f: impl FnOnce()) {
        let _lock = GUARD_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        if let Err(payload) = result {
            std::panic::resume_unwind(payload);
        }
    }

    /// Test-scoped guard wrapping `SolverThreadGuard` with a test-local
    /// counter. Assertions use the local counter instead of the global
    /// `LIVE_SOLVER_THREADS`, eliminating flakiness from concurrent test
    /// threads that also call `reserve_solver_thread_slot()`. Fixes #1930.
    ///
    /// Drop order: `TrackedGuard::drop` decrements the test-local counter,
    /// then `_inner` (SolverThreadGuard) is dropped automatically, which
    /// decrements the global counter. Observing the test-local counter
    /// reach 0 proves the full drop chain ran.
    struct TrackedGuard {
        _inner: SolverThreadGuard,
        counter: Arc<AtomicUsize>,
    }

    impl Drop for TrackedGuard {
        fn drop(&mut self) {
            self.counter.fetch_sub(1, Ordering::SeqCst);
        }
    }

    fn tracked_reserve(counter: &Arc<AtomicUsize>) -> TrackedGuard {
        let guard = reserve_solver_thread_slot();
        counter.fetch_add(1, Ordering::SeqCst);
        TrackedGuard {
            _inner: guard,
            counter: Arc::clone(counter),
        }
    }

    #[test]
    fn test_reserve_solver_thread_slot_increments() {
        with_serialized_guard_test(|| {
            let counter = Arc::new(AtomicUsize::new(0));
            let _guard = tracked_reserve(&counter);
            assert_eq!(
                counter.load(Ordering::SeqCst),
                1,
                "reserve should increment test-local counter"
            );
        });
    }

    #[test]
    fn test_solver_thread_guard_decrements_on_drop() {
        with_serialized_guard_test(|| {
            let counter = Arc::new(AtomicUsize::new(0));
            {
                let _guard = tracked_reserve(&counter);
                assert_eq!(counter.load(Ordering::SeqCst), 1, "Guard should increment");
            }
            assert_eq!(
                counter.load(Ordering::SeqCst),
                0,
                "Dropping SolverThreadGuard should decrement"
            );
        });
    }

    #[test]
    fn test_solver_thread_guard_multiple_guards() {
        with_serialized_guard_test(|| {
            let counter = Arc::new(AtomicUsize::new(0));
            let _g1 = tracked_reserve(&counter);
            let _g2 = tracked_reserve(&counter);
            let _g3 = tracked_reserve(&counter);
            assert_eq!(counter.load(Ordering::SeqCst), 3, "Three guards active");
            drop(_g2);
            assert_eq!(counter.load(Ordering::SeqCst), 2, "Dropped one guard");
            drop(_g1);
            drop(_g3);
            assert_eq!(counter.load(Ordering::SeqCst), 0, "All guards dropped");
        });
    }

    /// The critical test: SolverThreadGuard must decrement on panic.
    /// This is the exact bug #1706 identified — without RAII, a panic
    /// in the solver thread permanently inflates the counter.
    #[test]
    fn test_solver_thread_guard_decrements_on_panic() {
        with_serialized_guard_test(|| {
            let counter = Arc::new(AtomicUsize::new(0));
            let c = Arc::clone(&counter);
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _guard = tracked_reserve(&c);
                assert_eq!(c.load(Ordering::SeqCst), 1);
                panic!("simulated solver panic");
            }));
            assert!(result.is_err(), "Should have caught the panic");
            assert_eq!(
                counter.load(Ordering::SeqCst),
                0,
                "Guard must decrement even on panic (#1706)"
            );
        });
    }

    /// Verify the guard works correctly across thread boundaries.
    /// After #1710 fix: guard is reserved on parent thread and moved into
    /// the spawned thread. The counter is incremented immediately (not after
    /// the child thread starts), eliminating the TOCTOU race.
    #[test]
    fn test_solver_thread_guard_cross_thread() {
        with_serialized_guard_test(|| {
            let counter = Arc::new(AtomicUsize::new(0));
            let guard = tracked_reserve(&counter);
            assert_eq!(
                counter.load(Ordering::SeqCst),
                1,
                "Counter increments immediately on reserve, before spawn"
            );
            let handle = std::thread::spawn(move || {
                let _guard = guard;
                std::thread::sleep(std::time::Duration::from_millis(10));
            });
            handle.join().expect("Thread should complete without panic");
            assert_eq!(
                counter.load(Ordering::SeqCst),
                0,
                "Guard drop on thread exit should decrement"
            );
        });
    }

    /// Cross-thread panic: guard must decrement even when a spawned thread panics.
    #[test]
    fn test_solver_thread_guard_cross_thread_panic() {
        with_serialized_guard_test(|| {
            let counter = Arc::new(AtomicUsize::new(0));
            let guard = tracked_reserve(&counter);
            let handle = std::thread::spawn(move || {
                let _guard = guard;
                panic!("simulated cross-thread solver panic");
            });
            let result = handle.join();
            assert!(result.is_err(), "Thread should have panicked");
            assert_eq!(
                counter.load(Ordering::SeqCst),
                0,
                "Cross-thread panic must still decrement (#1706)"
            );
        });
    }

    /// Critical TOCTOU test: reservation must be atomic with the counter
    /// increment. When we reserve on the parent thread, the counter is
    /// immediately visible to other callers. This is the core #1710 fix.
    #[test]
    fn test_reserve_is_immediately_visible() {
        with_serialized_guard_test(|| {
            let counter = Arc::new(AtomicUsize::new(0));
            let _guard1 = tracked_reserve(&counter);
            assert_eq!(
                counter.load(Ordering::SeqCst),
                1,
                "First reservation immediately visible"
            );
            let _guard2 = tracked_reserve(&counter);
            assert_eq!(
                counter.load(Ordering::SeqCst),
                2,
                "Second reservation immediately visible"
            );
        });
    }

    #[test]
    fn test_reserve_solver_thread_slot_returns_immediately_when_capacity() {
        with_serialized_guard_test(|| {
            let start = std::time::Instant::now();
            let _guard = reserve_solver_thread_slot();
            let elapsed = start.elapsed();
            assert!(
                elapsed < std::time::Duration::from_secs(2),
                "reserve_solver_thread_slot should return quickly when under limit, took {:?}",
                elapsed
            );
        });
    }

    #[test]
    fn test_reserve_solver_thread_slot_no_oversubscribe_under_race() {
        with_serialized_guard_test(|| {
            const CONTENDERS: usize = 8;
            let start = Arc::new(Barrier::new(CONTENDERS));
            let active = Arc::new(AtomicUsize::new(0));
            let peak = Arc::new(AtomicUsize::new(0));

            let mut handles = Vec::new();
            for _ in 0..CONTENDERS {
                let start = Arc::clone(&start);
                let active = Arc::clone(&active);
                let peak = Arc::clone(&peak);
                handles.push(std::thread::spawn(move || {
                    start.wait();
                    let _guard = reserve_solver_thread_slot();
                    let now = active.fetch_add(1, Ordering::SeqCst) + 1;
                    peak.fetch_max(now, Ordering::SeqCst);
                    std::thread::sleep(std::time::Duration::from_millis(120));
                    active.fetch_sub(1, Ordering::SeqCst);
                }));
            }

            for handle in handles {
                handle.join().expect("contender thread should complete");
            }

            let peak_active = peak.load(Ordering::SeqCst);
            let cap = max_solver_threads();
            assert!(
                peak_active <= cap,
                "Limiter oversubscribed under contention: peak_active={peak_active}, max={cap}"
            );
        });
    }

    /// Far-out watchdog formula: `nominal + min(3 × nominal, 180s) + 10s
    /// grace`, mirroring ay's `install_quantifier_deadline_backstop`
    /// (ay 62695cfe04) so the external watchdog sits beyond ay's own
    /// worst-case deadline for deterministic-budget-governed solves.
    #[test]
    fn test_far_out_watchdog_default_is_130s() {
        assert_eq!(far_out_watchdog_timeout(None), Duration::from_secs(130));
    }

    #[test]
    fn test_far_out_watchdog_scales_with_small_rlimit() {
        // 1s nominal -> 1 + 3 + 10 = 14s.
        assert_eq!(
            far_out_watchdog_timeout(Some(1_000)),
            Duration::from_secs(14)
        );
    }

    #[test]
    fn test_far_out_watchdog_caps_backstop_extra_at_180s() {
        // 200s nominal -> extra capped at 180s -> 200 + 180 + 10 = 390s.
        assert_eq!(
            far_out_watchdog_timeout(Some(200_000)),
            Duration::from_secs(390)
        );
    }

    #[test]
    fn test_max_solver_threads_default() {
        let cap = max_solver_threads();
        assert!(
            cap >= 2,
            "max_solver_threads should be at least 2, got {cap}"
        );
    }

    #[test]
    fn test_default_max_solver_threads_is_half_cores() {
        let cores = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(2);
        let expected = (cores / 2).max(2);
        assert_eq!(
            default_max_solver_threads(),
            expected,
            "default should be num_cores/2 (min 2): cores={cores}"
        );
    }
}
