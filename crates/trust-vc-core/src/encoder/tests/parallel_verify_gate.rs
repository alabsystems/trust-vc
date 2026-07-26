// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the test-only verification gate (#2273, #2645).
//!
//! Default mode: parallel (no serialization).
//! `TRUST_VC_SEQUENTIAL_TESTS=1`: serialized (mutex-gated).

use super::*;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use crate::encoder::verification::test_gate::{
    register_current_thread_for_gate_observation, reset_gate_observation, ACTIVE_VERIFY_CALLS,
    MAX_ACTIVE_VERIFY_CALLS_SEEN,
};

/// Serializes the two gate tests against each other.
///
/// Both tests mutate `TRUST_VC_SEQUENTIAL_TESTS` (process-global env var)
/// and share static observation counters. Running them concurrently causes
/// `test_default_mode_allows_parallel_verification` to remove the env var
/// while `test_verify_gate_serializes_when_sequential_mode`'s threads are
/// executing, making the gate skip observation. Fixes race found by P1-865.
static GATE_TEST_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Proves the test gate serializes when `TRUST_VC_SEQUENTIAL_TESTS=1` is set.
///
/// Spawns 4 threads that each call `AYEncoder::verify()` concurrently,
/// then asserts that at most 1 is active inside the gate at any time.
#[test]
fn test_verify_gate_serializes_when_sequential_mode() {
    let _lock = GATE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());

    // Enable sequential mode for this test. GATE_TEST_MUTEX (held above)
    // serializes the two gate tests, so the guard's restore-on-drop is
    // race-free; the workspace env choke point performs the raw write.
    let _sequential_mode = crate::env::ScopedEnvVar::set("TRUST_VC_SEQUENTIAL_TESTS", "1");

    reset_gate_observation();

    let barrier = Arc::new(std::sync::Barrier::new(4));

    let handles: Vec<_> = (0..4)
        .map(|i| {
            let barrier = Arc::clone(&barrier);
            std::thread::spawn(move || {
                register_current_thread_for_gate_observation();

                let mut ctx = VerificationContext::new();
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("bound", format!("x > {i}")));
                ctx.push_obligation(ProofObligation::assert("positive", "x >= 0"));

                barrier.wait();
                let result = AYEncoder::verify(&ctx);
                expect_verified_or_unknown(&result, &format!("thread {i}"));
            })
        })
        .collect();

    for h in handles {
        h.join().expect("thread panicked");
    }

    let max_seen = MAX_ACTIVE_VERIFY_CALLS_SEEN.load(Ordering::SeqCst);
    assert_eq!(
        max_seen, 1,
        "sequential mode should serialize verification calls: max concurrent was {max_seen}, expected 1"
    );
}

/// Proves the sequential-mode gate fully recovers after unwind.
///
/// A panic inside `with_verify_test_gate()` must drop both the observation
/// guard and the reentrancy-depth guard. Otherwise the active-call counter can
/// remain stuck above zero or the next same-thread call can be misclassified as
/// reentrant and skip observation entirely.
#[test]
fn test_verify_gate_recovers_after_panic_unwind() {
    let _lock = GATE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());
    let _sequential_mode = crate::env::ScopedEnvVar::set("TRUST_VC_SEQUENTIAL_TESTS", "1");

    reset_gate_observation();
    register_current_thread_for_gate_observation();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::encoder::verification::test_gate::with_verify_test_gate(|| {
            assert_eq!(
                ACTIVE_VERIFY_CALLS.load(Ordering::SeqCst),
                1,
                "observed call should be active inside the sequential gate"
            );
            panic!("simulated verify-gate panic");
        });
    }));
    assert!(result.is_err(), "panic regression test should unwind");
    assert_eq!(
        ACTIVE_VERIFY_CALLS.load(Ordering::SeqCst),
        0,
        "VerifyGateObservationGuard must decrement after panic unwind"
    );

    reset_gate_observation();
    register_current_thread_for_gate_observation();
    crate::encoder::verification::test_gate::with_verify_test_gate(|| {
        assert_eq!(
            ACTIVE_VERIFY_CALLS.load(Ordering::SeqCst),
            1,
            "subsequent same-thread call should still be observed after unwind"
        );
    });
    let max_seen = MAX_ACTIVE_VERIFY_CALLS_SEEN.load(Ordering::SeqCst);
    assert_eq!(
        max_seen, 1,
        "VerifyGateDepthGuard must restore depth after panic so the next call is not treated as reentrant"
    );
}

/// Proves that the default mode allows parallel verification calls (#2645).
///
/// Spawns 4 threads that each call `AYEncoder::verify()` concurrently.
/// With the gate inverted (parallel by default), all threads complete
/// successfully without the mutex. The observation counters are only
/// active in sequential mode, so we verify thread completion instead.
#[test]
fn test_default_mode_allows_parallel_verification() {
    let _lock = GATE_TEST_MUTEX.lock().unwrap_or_else(|e| e.into_inner());

    // Ensure sequential mode is NOT set (unset for the test, restored on exit).
    let _sequential_mode = crate::env::ScopedEnvVar::unset("TRUST_VC_SEQUENTIAL_TESTS");

    let barrier = Arc::new(std::sync::Barrier::new(4));
    let completed = Arc::new(std::sync::atomic::AtomicUsize::new(0));

    let handles: Vec<_> = (0..4)
        .map(|i| {
            let barrier = Arc::clone(&barrier);
            let completed = Arc::clone(&completed);
            std::thread::spawn(move || {
                let mut ctx = VerificationContext::new();
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("bound", format!("x > {i}")));
                ctx.push_obligation(ProofObligation::assert("positive", "x >= 0"));

                barrier.wait();
                let result = AYEncoder::verify(&ctx);
                expect_verified_or_unknown(&result, &format!("thread {i}"));
                completed.fetch_add(1, Ordering::SeqCst);
            })
        })
        .collect();

    for h in handles {
        h.join().expect("thread panicked");
    }

    let done = completed.load(Ordering::SeqCst);
    assert_eq!(
        done, 4,
        "default parallel mode: expected all 4 threads to complete, got {done}"
    );
}
