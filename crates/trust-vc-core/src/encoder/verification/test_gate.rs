// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test-only verification gate for optional deterministic lib test execution.
//!
//! Under `#[cfg(test)]`, solver-backed tests run **parallel by default** — each
//! ay instance is fully independent with no shared global state (#2645).
//!
//! Set `TRUST_VC_SEQUENTIAL_TESTS=1` to re-enable the process-global mutex for
//! deterministic CI mode or timing-sensitive benchmarks.
//!
//! History: the gate was originally always-on (#2273) to work around ay-dpll
//! non-determinism under parallel thread contention. Root cause was thread-local
//! state leakage (now fixed), not ay thread safety. `verify_batch_parallel`
//! (#2647) proved independent ay instances produce correct results in parallel.
//!
//! Part of #2273, #2645.

#[cfg(test)]
use std::cell::Cell;
#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(test)]
static VERIFY_TEST_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

#[cfg(test)]
std::thread_local! {
    static VERIFY_GATE_DEPTH: Cell<usize> = const { Cell::new(0) };
}

/// Test-only counter: number of verification calls currently inside the gate.
/// Used by `parallel_verify_gate` regression tests to prove serialization.
#[cfg(test)]
pub(in crate::encoder) static ACTIVE_VERIFY_CALLS: AtomicUsize = AtomicUsize::new(0);

/// Test-only high-water mark: maximum concurrent verification calls observed.
/// Used by `parallel_verify_gate` regression tests.
#[cfg(test)]
pub(in crate::encoder) static MAX_ACTIVE_VERIFY_CALLS_SEEN: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
fn observed_threads() -> &'static std::sync::Mutex<std::collections::HashSet<std::thread::ThreadId>>
{
    static OBSERVED_THREADS: std::sync::OnceLock<
        std::sync::Mutex<std::collections::HashSet<std::thread::ThreadId>>,
    > = std::sync::OnceLock::new();
    OBSERVED_THREADS.get_or_init(|| std::sync::Mutex::new(std::collections::HashSet::new()))
}

#[cfg(test)]
fn current_thread_is_observed() -> bool {
    let current_thread = std::thread::current().id();
    observed_threads()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .contains(&current_thread)
}

#[cfg(test)]
struct VerifyGateDepthGuard {
    reentrant: bool,
}

#[cfg(test)]
impl VerifyGateDepthGuard {
    fn enter() -> Self {
        let reentrant = VERIFY_GATE_DEPTH.with(|depth| {
            let current = depth.get();
            depth.set(current + 1);
            current > 0
        });
        Self { reentrant }
    }
}

#[cfg(test)]
impl Drop for VerifyGateDepthGuard {
    fn drop(&mut self) {
        VERIFY_GATE_DEPTH.with(|depth| {
            let current = depth.get();
            debug_assert!(current > 0, "verify gate depth should always be positive");
            depth.set(current.saturating_sub(1));
        });
    }
}

#[cfg(test)]
struct VerifyGateObservationGuard {
    observing: bool,
}

#[cfg(test)]
impl VerifyGateObservationGuard {
    fn enter() -> Self {
        if !current_thread_is_observed() {
            return Self { observing: false };
        }

        let active = ACTIVE_VERIFY_CALLS.fetch_add(1, Ordering::SeqCst) + 1;
        let _ = MAX_ACTIVE_VERIFY_CALLS_SEEN.fetch_max(active, Ordering::SeqCst);
        Self { observing: true }
    }
}

#[cfg(test)]
impl Drop for VerifyGateObservationGuard {
    fn drop(&mut self) {
        if self.observing {
            ACTIVE_VERIFY_CALLS.fetch_sub(1, Ordering::SeqCst);
        }
    }
}

/// Clears the test-only gate observation state for a fresh assertion window.
#[cfg(test)]
pub(in crate::encoder) fn reset_gate_observation() {
    let active = ACTIVE_VERIFY_CALLS.load(Ordering::SeqCst);
    assert_eq!(
        active, 0,
        "cannot reset gate observation while {active} observed verification calls remain active"
    );
    observed_threads()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clear();
    MAX_ACTIVE_VERIFY_CALLS_SEEN.store(0, Ordering::SeqCst);
}

/// Opts the current thread into the test-only gate observation counters.
#[cfg(test)]
pub(in crate::encoder) fn register_current_thread_for_gate_observation() {
    observed_threads()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .insert(std::thread::current().id());
}

/// Wraps a verification closure in the test gate.
///
/// In test builds: runs parallel by default. When `TRUST_VC_SEQUENTIAL_TESTS=1`
/// is set, acquires `VERIFY_TEST_MUTEX` to serialize solver-backed calls.
///
/// In non-test builds: passes through with zero overhead.
#[cfg(test)]
pub(in crate::encoder) fn with_verify_test_gate<T>(f: impl FnOnce() -> T) -> T {
    if std::env::var_os("TRUST_VC_SEQUENTIAL_TESTS").is_some() {
        let depth_guard = VerifyGateDepthGuard::enter();
        if depth_guard.reentrant {
            return f();
        }

        let _mutex_guard = VERIFY_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
        let _observation_guard = VerifyGateObservationGuard::enter();
        return f();
    }
    f()
}

#[cfg(not(test))]
pub(in crate::encoder) fn with_verify_test_gate<T>(f: impl FnOnce() -> T) -> T {
    f()
}
