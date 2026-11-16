//! Solver-thread capacity and timeout control.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use crate::solver_budget::ConflictBudget;

/// Hard timeout for BV solver queries that bypass ay-dpll's internal timeout.
///
/// ay-dpll's BV solver calls `SatSolver::solve()` (non-interruptible) instead of
/// `solve_interruptible()`, so the solver-level timeout set via `with_limits()` is
/// ignored during BV SAT solving (#1605, #1682). This thread-based timeout ensures
/// verification always terminates by running `check_sat()` in a separate thread
/// and joining with a deadline.
///
/// Set well below the old 30s to prevent timeout accumulation across the full
/// test suite (#1682): with ~870 solver invocations across ~1,045 individual
/// assertions, a large cap accumulates only on the (few) deliberately-stuck
/// cases, but those exist. The cap must still clear the HARDEST solvable
/// problems on the SLOWEST supported host: the unsigned div/rem identity
/// proofs measure ~40s each in an unloaded DEBUG build on a Grace GB10
/// (Linux/aarch64, 2026-08-19), where the old 10s cap — tuned to the ~5-8s
/// the same proofs need on an M-series mac — failed genuinely-verifying
/// cases (bitvector_rs_verified_subset red on the first clean-build sweep).
/// 60s clears the measured worst case with headroom; a problem that has not
/// finished in 60s is stuck in exponential BV DPLL search.
pub(in crate::encoder) const BV_HARD_TIMEOUT: Duration = Duration::from_secs(60);

/// Default DETERMINISTIC per-solve conflict budget handed to ay via
/// `with_limits()` when the verification context carries no explicit
/// `#[verifier::rlimit(N)]`. This — not the wall clock below — is the bound
/// that is meant to decide a runaway solve.
///
/// VALUE, AND WHY IT IS NOT LOWER. 400k is exactly ay's own
/// `Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE`, the per-SAT-solve allowance
/// ay already applies by default. Making it explicit here changes NOTHING
/// about which proofs succeed — it is deliberately a no-op on capability —
/// while moving the number under trust-vc's control, into the VC cache key,
/// and under `#[verifier::rlimit]` override. Lowering it is what would cost
/// capability (silently converting proofs to `Unknown`), so the migration
/// does not lower it.
///
/// MEASURED HEADROOM (2026-08-20, this repo, debug build, cache off, load
/// average 7.4). Instrumented every `check_sat` in
/// `collection_mutation_loop_soundness` — the harness carrying the four
/// obligations whose verdicts rotate with machine load, and therefore the
/// worst case that matters here. 205 solves:
///
/// | conflicts | solves |
/// |-----------|--------|
/// | 0         | 171    |
/// | 1-12      | 27     |
/// | 60-143    | 5      |
/// | 292, 317  | 2      |
///
/// Maximum 317 conflicts; maximum 2,872 decisions. This allowance is ~1,260x
/// the heaviest solve measured. ay's own calibration note records the same
/// shape from the other side (1,104 check-sat solves across its heavy suite,
/// max 2,208 conflicts per solver lifetime, nothing above 10k; the heaviest
/// known real trust-vc workload, the calc.rs line93 seq-chain BV<->LIA
/// bridge, at ~1,266 conflicts). Nothing legitimate is anywhere near this
/// number, which is exactly the property a fail-closed budget needs: it
/// bounds divergence without ever being the reason a real proof fails.
///
/// THE SAME MEASUREMENT SHOWS WHAT THIS BUDGET DOES NOT FIX. Those 205 solves
/// took up to 46,160 MILLISECONDS of wall clock while doing at most 317
/// conflicts of work, against a 30,000ms wall. So for this family the wall is
/// still the deciding bound and the work budget is nowhere near spent — their
/// cost is E-matching, preprocessing and certificate minting, none of which a
/// conflict budget can see. This budget makes conflict-driven divergence
/// deterministic; it does not make that family deterministic. See
/// [`DEFAULT_SOLVER_WALL_BACKSTOP_MS`] for the experiment that established
/// this and the raise that did NOT fix it.
pub(in crate::encoder) const DEFAULT_CONFLICT_BUDGET_CONFLICTS: u64 = 400_000;

/// Default WALL-CLOCK backstop handed to ay via `with_limits()` when the
/// verification context carries no explicit override.
///
/// THIS IS A LIVENESS BACKSTOP, NOT A VERDICT BOUNDARY. A pure conflict
/// budget gives no wall guarantee: a solve can spin in preprocessing, in a
/// theory-propagation loop, or in certificate minting without accruing
/// conflicts, so removing the wall entirely would trade nondeterminism for
/// hangs. It is therefore kept — and deliberately set far enough above the
/// work budget that it fires only pathologically.
///
/// WHY IT IS STILL 30s, AND WHAT THAT COSTS. Raising it was the obvious
/// companion to this migration and it is deliberately NOT part of it,
/// because the experiment that would have justified the raise came back
/// null. Both halves are recorded here so the next attempt does not repeat
/// the guess.
///
/// THE HYPOTHESIS. The four `collection_mutation_loop_soundness`
/// obligations whose verdicts rotate with machine load do NOT fail with a
/// timeout reason — measured, they fail with
/// `unknown ((incomplete self-check-rejected))`, reason text "computed UNSAT
/// rejected by mandatory strict certification: strict UNSAT proof validation
/// failed: step t0 uses unverified trust rule; deferred-trust discharge
/// failed: … the authored assertions could not be independently re-solved as
/// UNSAT". Reading ay: that discharge step re-solves the authored obligation
/// in a fresh executor (`unsat_cert.rs` step (4), `reconfirms_unsat_within`)
/// and the re-solve inherits the CALLER's deadline
/// (`set_solve_controls(.., self.solve_deadline.get())`). So a caller wall
/// that expires mid-certification withholds a CORRECT unsat ay already
/// computed. ay's own note on the same funnel says the margin is thin: a
/// 5.85s re-solve under an 8s effective wall at 1.37x, and "contention
/// slowing the box past ~1.4x flips a correct `unsat` to `unknown`".
///
/// THE MEASUREMENT THAT SUPPORTED IT. Instrumented wall time over 205 solves
/// of that harness (load average 7.4): five exceeded 20s and the ceiling was
/// 46,160ms — already past this 30,000ms bound — while the same solves did at
/// most 317 conflicts of work.
///
/// THE NULL. Raising this constant to 180,000ms (6x, ~3.9x the measured
/// ceiling) did not stop the rotation: the harness still failed 2 of the 4.
/// One post-change run against three baseline runs of 3/2/3 failures is not
/// enough to call it worse, but it is nowhere near enough to call it better,
/// and the raise is not free — the wall is also the suite's latency floor for
/// a divergent solve and it feeds the far-out watchdog
/// (`nominal + min(3 x nominal, 180s) + 10s`), so 180s here would mean a 370s
/// external hang deadline on every quantified obligation. An envelope
/// widening on EVERY solve, justified by a mechanism that did not reproduce,
/// is not a change worth its blast radius.
///
/// WHAT THIS LEAVES OPEN, HONESTLY. With the wall at 30s and the work budget
/// at 400k conflicts, the wall is still the bound that decides these solves —
/// they are ~0.08% of the way through their budget when it fires. The
/// deterministic budget genuinely governs a CONFLICT-heavy divergence; it
/// does not govern this family, whose cost is E-matching, preprocessing and
/// certificate minting rather than conflicts. Closing that properly needs a
/// deterministic bound on THAT work — an ay-side concern — not a bigger
/// number here.
///
/// RE-READ 2026-09-15 (ay pin 4cadc2bf, sibling 0dc8f8f0). Part of what the
/// paragraphs above measured was NOT this wall's size but WHO applied it:
/// ay 6226726f3 (2026-08-22, an ancestor of every 0.26.0 pin) made the
/// quantified far-out backstop (`install_quantifier_deadline_backstop`,
/// mirrored by [`far_out_watchdog_timeout`] below) an OPT-IN that is OFF by
/// default, and `AYEncoder::with_limits` did not opt in until 2026-09-15. So
/// from the 0.26.0 pin (2026-09-11) a quantified solve here had exactly this
/// 30 s of wall, while the far-out watchdog kept mirroring an extension ay
/// was not applying — the two same-index read-back controls the retired
/// ay-pin quarantine held were timing out on that bare wall under load.
/// `with_limits` now opts in (the effective quantified wall is `30 s +
/// min(90 s, 180 s)` = 120 s, the number the watchdog was already derived
/// from); the measured effect on those two controls is in the ledger row of
/// that date. The constant itself is unchanged.
/// RE-MEASURED 2026-09-15 (later the same day, ay pin `4cadc2bf`, sibling
/// `0dc8f8f0`) — **the value moves to 120 s and the opt-in above is
/// WITHDRAWN, because the two were an incoherent envelope.** The backstop
/// widens ay's SEARCH wall and nothing else; ay keeps TWO deadline cells and
/// only one of them is widened:
///
/// * `Solver::install_solve_controls` -> `Executor::set_solve_controls`
///   (`api/solving/check.rs:434`, `executor/check_sat.rs:2949-2958`) sets
///   BOTH `solve_deadline` AND `certification_deadline` to `now + nominal`.
/// * `install_quantifier_deadline_backstop` (`check_sat.rs:3125-3172`)
///   extends `solve_deadline` ALONE — the write is
///   `self.solve_deadline.set(Some(backstop))` — so the search may run to
///   `nominal + min(3 x nominal, 180 s)` while the certification envelope
///   still expires at `nominal`.
/// * `restore_timeout_deadline_after_call` (`check_sat.rs:3174-3187`, called
///   from `check_sat` at `:1616`) then puts the ALREADY-EXPIRED nominal
///   deadline back before the funnel runs.
/// * `certify_unsat_for_publication` (`check.rs:575`) polls
///   `certification_deadline` (`executor/unsat_cert.rs` `resources_live`,
///   `TrustClauseDischargeControls::deadline`) and refuses a correct UNSAT
///   with "step tN uses unverified trust rule"; then
///   `finish_verified_result` -> `decline_definite_publication_on_external_stop`
///   (`executor/lifecycle/unknown_publication.rs:107-115`) reads the restored
///   `solve_deadline` through `should_abort_theory_loop`
///   (`check_sat.rs:3220-3243`) and REVOKES any definite verdict as
///   `Unknown(Timeout)`.
///
/// NET, with a 30 s nominal and the backstop on: a quantified solve that
/// takes more than ~30 s of wall CANNOT publish a definite answer by either
/// route, however well the search went. That is not a hypothesis — ay records
/// the same skew from the other side, on this repo's own obligation, at
/// `check_sat.rs:2862-2886`: "Measured on trust-vc's `push_appends_entailed`
/// obligation: `certification_deadline_remaining_ms=0` beside
/// `solve_deadline_remaining_ms=11094`".
///
/// MEASURED CONSEQUENCE (25 runs at `3287a67f`, the commit that turned the
/// opt-in on): `floor_push_appends_entailed_verified` run alone was RED 4 of
/// 5 — including at 1-minute load average 6.77 — and 3 of 3 under load;
/// `replay_push_appends_entailed_verified` 1 of 3 alone and 3 of 3 under
/// load. 8 of the 14 reds were `Timeout` (the publication revocation) and 3
/// were `ConfirmationDisagree` (the certification refusal, reached through
/// the confirm solve). Both categories are the SAME boundary with two exit
/// doors, which is why the opt-in "closed the timeout half" and did not.
///
/// THE FIX IS TO ASK FOR THE WALL WE ACTUALLY WANT. `set_timeout` is the one
/// control that moves BOTH cells, so the nominal becomes 120 s — exactly the
/// envelope the backstop was buying at 30 s — and the widener is switched
/// off in [`crate::encoder::AYEncoder::with_limits`]. Search budget: the same
/// 120 s. Certification and publication: now the same 120 s instead of an
/// expired 30 s. Worst-case latency: 120 s instead of 300 s (the backstop
/// would have extended a 120 s nominal to 120 + 180). The external watchdog
/// is unchanged at 130 s because it now derives from a nominal that needs no
/// mirror (see [`far_out_watchdog_timeout`]).
///
/// AND THE NULL ABOVE IS NOT EVIDENCE AGAINST THIS. That 180 s experiment
/// predates both the backstop opt-in and ay's `certification_deadline` split
/// (`f704330f29`, 2026-09-01): it raised the search wall while the funnel
/// that refuses late UNSATs did not exist yet in the form measured here. The
/// number changed for a mechanism, not as a guess; the measurement that
/// justifies it is the loaded repro rate recorded in the ledger row of this
/// date.
pub(in crate::encoder) const DEFAULT_SOLVER_WALL_BACKSTOP_MS: u64 = 120_000;

/// ay's quantified deadline backstop used to be mirrored here with its own
/// `FACTOR`/`MAX_EXTRA` constants, so the external watchdog could sit beyond
/// the widened SEARCH deadline. The mirror is gone with the widener:
/// `AYEncoder::with_limits` no longer opts in (it widens `solve_deadline`
/// only, leaving `certification_deadline` at the nominal — see
/// [`DEFAULT_SOLVER_WALL_BACKSTOP_MS`]), so ay's own deadline for a
/// trust-vc solve IS the nominal wall and the watchdog derives from it
/// directly. Re-adding a mirror here without re-reading that note would
/// re-create the skew.
///
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
/// work on any machine), and a flat 10s external watchdog re-introduced the
/// wall clock as the PRIMARY truncation and made ported-gate verdicts flip
/// with CPU load (the calc.rs seq-chain flake, and the nonlinear.rs test5
/// flip under a loaded suite run). For these obligations the external
/// watchdog is therefore derived from the nominal solver budget the encoder
/// actually configured (`with_limits`, see
/// [`DEFAULT_SOLVER_WALL_BACKSTOP_MS`]) plus a grace period: it can only fire
/// when ay has failed to honor its own deadline — true hang protection, never
/// a verdict boundary.
///
/// THE DERIVATION IS NOW DIRECT (2026-09-15, later the same day). It used to
/// mirror ay's quantified backstop formula (`nominal + min(3 x nominal,
/// 180s)`) because `with_limits` opted in to that widener. It no longer does:
/// the widener moves ay's SEARCH deadline without moving its CERTIFICATION
/// deadline, so trust-vc asks for the wall it wants through `set_timeout`
/// (which moves both) and ay's deadline for a trust-vc solve is exactly the
/// nominal. See [`DEFAULT_SOLVER_WALL_BACKSTOP_MS`] for the ay call chain and
/// the measurement.
///
/// With the defaults this is 120s + 10s = 130s — the same external ceiling as
/// the mirrored form it replaces. It scales with an explicit `rlimit_ms`
/// exactly like ay's own `set_timeout` deadline does.
pub(in crate::encoder) fn far_out_watchdog_timeout(rlimit_ms: Option<u64>) -> Duration {
    far_out_nominal_timeout(rlimit_ms) + FAR_OUT_WATCHDOG_GRACE
}

/// The SOLVER-INTERNAL deadline ay applies to a trust-vc solve: the nominal
/// wall `AYEncoder::with_limits` installed through `Solver::set_timeout`,
/// which ay copies into BOTH its `solve_deadline` and its
/// `certification_deadline` (`executor/check_sat.rs:2949-2958`). No widener
/// is opted in, so there is nothing else to mirror. The external watchdog
/// adds `FAR_OUT_WATCHDOG_GRACE` on top so it can only fire when ay has
/// failed to honor that deadline.
fn far_out_nominal_timeout(rlimit_ms: Option<u64>) -> Duration {
    Duration::from_millis(rlimit_ms.unwrap_or(DEFAULT_SOLVER_WALL_BACKSTOP_MS))
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

/// Resolve the DETERMINISTIC conflict budget for a solve.
///
/// `None` (no `#[verifier::rlimit]`) resolves to the calibrated default —
/// never to "no budget". The distinction matters at the ay boundary, where
/// "no budget" (`:rlimit 0`) additionally switches off ay's own default
/// ground allowance; see [`crate::solver_budget::ConflictBudget`].
pub(in crate::encoder) fn effective_conflict_budget(
    requested: Option<ConflictBudget>,
) -> ConflictBudget {
    requested.unwrap_or(ConflictBudget::Bounded(DEFAULT_CONFLICT_BUDGET))
}

/// Typed form of [`DEFAULT_CONFLICT_BUDGET_CONFLICTS`].
const DEFAULT_CONFLICT_BUDGET: std::num::NonZeroU64 =
    match std::num::NonZeroU64::new(DEFAULT_CONFLICT_BUDGET_CONFLICTS) {
        Some(budget) => budget,
        // A zero default would reach ay as `:rlimit 0` — "no limit, and no
        // default ground budget either" — i.e. the exact opposite of a
        // default. Fail the build instead.
        None => panic!("invariant: the default conflict budget must be non-zero"),
    };

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
                return SolverThreadGuard {
                    #[cfg(test)]
                    capacity_admitted: true,
                };
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
    SolverThreadGuard {
        #[cfg(test)]
        capacity_admitted: false,
    }
}

/// RAII guard that decrements `LIVE_SOLVER_THREADS` on drop, even if the
/// thread panics. Without this, a panic in `verify_assertion` would leave
/// the counter permanently inflated, eventually deadlocking the limiter.
///
/// Created by `reserve_solver_thread_slot()`, which increments the counter
/// on the calling thread before returning this guard. The guard is then
/// moved into the spawned thread so the decrement happens when the thread
/// exits (or panics). Fixes #1710.
pub(in crate::encoder) struct SolverThreadGuard {
    #[cfg(test)]
    capacity_admitted: bool,
}

impl Drop for SolverThreadGuard {
    fn drop(&mut self) {
        LIVE_SOLVER_THREADS.fetch_sub(1, Ordering::AcqRel);
    }
}

#[cfg(test)]
thread_local! {
    static TIMING_HAS_ADMITTED_SLOT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Reserve normal work unless this same thread already holds the timing
/// scope's genuinely capacity-admitted reservation. No permit is exported.
#[cfg(test)]
pub(in crate::encoder) fn reserve_solver_thread_slot_for_current_work() -> Option<SolverThreadGuard>
{
    if TIMING_HAS_ADMITTED_SLOT.with(std::cell::Cell::get) {
        None
    } else {
        Some(reserve_solver_thread_slot())
    }
}

/// Own one existing reservation outside the corpus's measurement window.
/// Only a successful capacity CAS can establish same-thread borrowing.
#[cfg(test)]
pub(in crate::encoder) fn with_timing_solver_admission<T>(
    f: impl FnOnce(Duration, bool) -> T,
) -> T {
    // Keep the existing optional gate outside capacity acquisition. The
    // default remains parallel; sequential mode keeps its original reentry.
    super::test_gate::with_verify_test_gate(|| timing_solver_admission_inner(f))
}

#[cfg(test)]
fn timing_solver_admission_inner<T>(f: impl FnOnce(Duration, bool) -> T) -> T {
    if TIMING_HAS_ADMITTED_SLOT.with(std::cell::Cell::get) {
        return f(Duration::ZERO, true);
    }
    let started = std::time::Instant::now();
    let owner = reserve_solver_thread_slot();
    let waited = started.elapsed();
    if !owner.capacity_admitted {
        // The original overload fallback is counted, but did not acquire
        // capacity. It cannot authorize borrowing. Release this outer probe;
        // ordinary verification keeps its existing reservation/fallback path.
        drop(owner);
        return f(waited, false);
    }
    struct BorrowScope<'a> {
        _owner: &'a SolverThreadGuard,
        _same_thread: std::marker::PhantomData<std::rc::Rc<()>>,
    }
    impl Drop for BorrowScope<'_> {
        fn drop(&mut self) {
            TIMING_HAS_ADMITTED_SLOT.with(|held| held.set(false));
        }
    }
    TIMING_HAS_ADMITTED_SLOT.with(|held| {
        assert!(
            !held.replace(true),
            "timing admission cannot replace a live owner"
        );
    });
    let _borrow = BorrowScope {
        _owner: &owner,
        _same_thread: std::marker::PhantomData,
    };
    f(waited, true)
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

    /// Far-out watchdog formula: `nominal + 10s grace`. ay's deadline for a
    /// trust-vc solve is the nominal wall `with_limits` installed (no widener
    /// is opted in — see `DEFAULT_SOLVER_WALL_BACKSTOP_MS`), so the external
    /// watchdog sits just beyond it and can only fire on a genuine hang.
    /// 130s here is the same external ceiling as the mirrored 30+90+10 form
    /// it replaces.
    #[test]
    fn test_far_out_watchdog_default_is_130s() {
        assert_eq!(far_out_watchdog_timeout(None), Duration::from_secs(130));
    }

    /// The default must resolve to a BOUNDED budget. A `None` that reached ay
    /// as `:rlimit 0` would mean "no limit, and disable ay's own default
    /// ground budget too" — strictly weaker than having no override at all.
    #[test]
    fn absent_override_resolves_to_the_bounded_default_never_to_unbounded() {
        assert_eq!(
            effective_conflict_budget(None).conflicts(),
            Some(DEFAULT_CONFLICT_BUDGET_CONFLICTS)
        );
    }

    #[test]
    fn explicit_unbounded_override_survives_resolution() {
        assert_eq!(
            effective_conflict_budget(Some(ConflictBudget::AyDefault)),
            ConflictBudget::AyDefault
        );
    }

    /// Headroom over the measured ceiling, stated as a test so lowering the
    /// budget has to confront the number that justified it. Too low silently
    /// converts proofs into `Unknown`.
    #[test]
    fn conflict_budget_keeps_three_orders_of_magnitude_over_measured_worst() {
        // Measured ceiling over the calibration harness: 317 conflicts.
        const MEASURED_WORST_CONFLICTS: u64 = 317;
        let configured_budget = std::hint::black_box(DEFAULT_CONFLICT_BUDGET_CONFLICTS);
        let measured_worst = std::hint::black_box(MEASURED_WORST_CONFLICTS);
        assert!(
            configured_budget >= 100 * measured_worst,
            "conflict budget {DEFAULT_CONFLICT_BUDGET_CONFLICTS} leaves less \
             than 100x margin over the measured {MEASURED_WORST_CONFLICTS}-conflict \
             worst case"
        );
    }

    #[test]
    fn test_far_out_watchdog_scales_with_small_rlimit() {
        // 1s nominal -> 1 + 10 = 11s. An explicit `#[verifier::rlimit]` wall
        // is the whole envelope, exactly as the default one is.
        assert_eq!(
            far_out_watchdog_timeout(Some(1_000)),
            Duration::from_secs(11)
        );
    }

    /// A generous explicit wall is not multiplied. Under the withdrawn
    /// mirror a 200s `rlimit_ms` produced a 390s external deadline, because
    /// ay's widener could have extended the search that far — while ay's
    /// certification envelope stayed at 200s. With one envelope the watchdog
    /// is 210s and every gate reads the same 200s.
    #[test]
    fn far_out_watchdog_does_not_multiply_an_explicit_wall() {
        assert_eq!(
            far_out_watchdog_timeout(Some(200_000)),
            Duration::from_secs(210)
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

    /// Borrow the same real owner through the ordinary native verification path,
    /// including nested timing scopes; no second reservation is returned.
    #[test]
    fn timing_admission_reuses_owner_for_nested_native_verification() {
        with_serialized_guard_test(|| {
            with_timing_solver_admission(|_, admitted| {
                assert!(admitted, "test needs an actual capacity-admitted owner");
                assert!(reserve_solver_thread_slot_for_current_work().is_none());
                with_timing_solver_admission(|waited, nested_admitted| {
                    assert!(nested_admitted);
                    assert_eq!(waited, Duration::ZERO);
                    assert!(reserve_solver_thread_slot_for_current_work().is_none());
                    let mut ctx = crate::vc::VerificationContext::new();
                    ctx.declare_var_typed("flag", crate::ir::TrustVcType::Bool);
                    ctx.push_obligation(crate::vc::ProofObligation::assume("yes", "flag"));
                    ctx.push_obligation(crate::vc::ProofObligation::assert("same", "flag"));
                    assert!(crate::encoder::AYEncoder::verify(&ctx).is_verified());
                });
                assert!(reserve_solver_thread_slot_for_current_work().is_none());
            });
            let outside = reserve_solver_thread_slot_for_current_work();
            assert!(
                outside.is_some(),
                "scope exit must restore ordinary reservation"
            );
            drop(outside);
        });
    }

    /// An unwind revokes same-thread borrowing before the existing owner drops.
    #[test]
    fn timing_admission_restores_ordinary_reservation_after_unwind() {
        with_serialized_guard_test(|| {
            let failed = std::panic::catch_unwind(|| {
                with_timing_solver_admission(|_, admitted| {
                    assert!(admitted, "test needs an actual capacity-admitted owner");
                    assert!(reserve_solver_thread_slot_for_current_work().is_none());
                    panic!("unwind inside a timing admission");
                });
            });
            assert!(failed.is_err());
            let outside = reserve_solver_thread_slot_for_current_work();
            assert!(outside.is_some(), "panic must not leave borrowing enabled");
            drop(outside);
        });
    }

    /// A different worker never inherits the parent's borrowing marker. Its
    /// ordinary guard remains Send and owns a distinct counted reservation.
    #[test]
    fn timing_admission_does_not_lend_ownership_to_unrelated_worker() {
        with_serialized_guard_test(|| {
            with_timing_solver_admission(|_, admitted| {
                assert!(admitted, "test needs an actual capacity-admitted owner");
                let worker = std::thread::spawn(|| {
                    let own = reserve_solver_thread_slot_for_current_work()
                        .expect("another thread must reserve its own capacity");
                    let owner_drop = std::thread::spawn(move || drop(own));
                    owner_drop
                        .join()
                        .expect("the existing owned guard remains Send");
                });
                worker.join().expect("unrelated worker should complete");
                assert!(reserve_solver_thread_slot_for_current_work().is_none());
            });
        });
    }
}
