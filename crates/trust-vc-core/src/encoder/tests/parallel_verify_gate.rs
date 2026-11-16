// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the test-only verification gate (#2273, #2645).
//!
//! Default mode: parallel (no serialization).
//! `TRUST_VC_SEQUENTIAL_TESTS=1`: serialized (mutex-gated).
//! Each configuration control runs in a fresh exact-test child, so it does not
//! change the parent suite's process environment or observation counters.

use super::*;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use crate::encoder::verification::test_gate::{
    register_current_thread_for_gate_observation, reset_gate_observation, ACTIVE_VERIFY_CALLS,
    MAX_ACTIVE_VERIFY_CALLS_SEEN,
};

const GATE_CHILD_TEST: &str = "TVC_VERIFY_GATE_CHILD_TEST";

/// Exercise the real environment-selected gate in an isolated process.
/// `Command::env` configures only the child; ordinary concurrent parent tests
/// retain their original gate mode. The original body runs exactly once in
/// the child selected by the same libtest image and exact test name.
fn run_gate_control_in_child(test_name: &str, sequential: bool, body: fn()) {
    if std::env::var_os(GATE_CHILD_TEST).is_some_and(|name| name == test_name) {
        if sequential {
            assert_eq!(
                std::env::var_os("TRUST_VC_SEQUENTIAL_TESTS"),
                Some("1".into())
            );
        } else {
            assert!(std::env::var_os("TRUST_VC_SEQUENTIAL_TESTS").is_none());
        }
        body();
        return;
    }
    assert!(
        std::env::var_os(GATE_CHILD_TEST).is_none(),
        "a gate-control child must select its exact original test"
    );
    let original_mode = std::env::var_os("TRUST_VC_SEQUENTIAL_TESTS");
    let module = module_path!()
        .split_once("::")
        .map_or(module_path!(), |(_, rest)| rest);
    let exact = format!("{module}::{test_name}");
    let mut command = std::process::Command::new(
        std::env::current_exe().expect("current gate-control libtest image"),
    );
    command
        .args(["--exact", &exact, "--nocapture"])
        .env(GATE_CHILD_TEST, test_name);
    if sequential {
        command.env("TRUST_VC_SEQUENTIAL_TESTS", "1");
    } else {
        command.env_remove("TRUST_VC_SEQUENTIAL_TESTS");
    }
    let output = command.output().expect("run the exact gate-control child");
    assert_eq!(
        std::env::var_os("TRUST_VC_SEQUENTIAL_TESTS"),
        original_mode,
        "a child gate control must not alter the parent process mode"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let expected_row = format!("test {exact} ... ok");
    assert!(
        output.status.success()
            && stdout.lines().any(|line| line == expected_row)
            && stdout.lines().any(|line| line
                .starts_with("test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; ")),
        "gate-control child {exact} failed ({status}):\n{stdout}\n{stderr}",
        status = output.status
    );
}

/// Proves the test gate serializes when `TRUST_VC_SEQUENTIAL_TESTS=1` is set.
///
/// Spawns 4 threads that each call `AYEncoder::verify()` concurrently,
/// then asserts that at most 1 is active inside the gate at any time.
#[test]
fn test_verify_gate_serializes_when_sequential_mode() {
    run_gate_control_in_child(
        "test_verify_gate_serializes_when_sequential_mode",
        true,
        verify_gate_serializes_when_sequential_mode_body,
    );
}

fn verify_gate_serializes_when_sequential_mode_body() {
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
    run_gate_control_in_child(
        "test_verify_gate_recovers_after_panic_unwind",
        true,
        verify_gate_recovers_after_panic_unwind_body,
    );
}

fn verify_gate_recovers_after_panic_unwind_body() {
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
    run_gate_control_in_child(
        "test_default_mode_allows_parallel_verification",
        false,
        default_mode_allows_parallel_verification_body,
    );
}

fn default_mode_allows_parallel_verification_body() {
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
