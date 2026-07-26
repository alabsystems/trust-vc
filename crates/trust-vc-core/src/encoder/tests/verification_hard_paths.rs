//! Tests for hard-to-reach verification pipeline paths (#1733):
//!
//! 1. BV_HARD_TIMEOUT expiration (recv_timeout Timeout branch)
//! 2. RecvTimeoutError::Disconnected (non-ay solver thread panic)
//! 3. Variable-divisor division-by-zero through full pipeline
//! 4. Real ay sort mismatch through catch_ay_sort_panics
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::verification::outcome::AssertionOutcome;
use crate::encoder::verification::unknown_category::UnknownCategory;
use crate::error::TrustVcResult;
use ay_dpll::UnknownReason;

// ============================================================
// 1. BV_HARD_TIMEOUT recv_timeout path
// ============================================================

/// Unit test for the channel timeout → Unknown conversion mechanism.
///
/// This validates the mpsc recv_timeout mechanics and BV_HARD_TIMEOUT
/// import, NOT the production code path in verify_assertion_with_timeout_typed.
/// The match/format string here is a replica of the timeout branch in
/// `verify_assertion_with_timeout_typed`.
/// If the production format string changes, this test will NOT detect it.
///
/// A full integration test triggering a real BV timeout would require
/// >10s per run and be flaky across machines.
///
/// DISCRIMINATING: This test fails if:
/// - BV_HARD_TIMEOUT constant is removed or changes type
/// - The mpsc timeout mechanism stops producing RecvTimeoutError::Timeout
///   NOT discriminating for: production format string drift in assertion.rs
#[test]
fn test_bv_hard_timeout_channel_pattern_returns_unknown() {
    use crate::encoder::verification::timeout::BV_HARD_TIMEOUT;

    // Use a shorter timeout for the test to avoid 10s+ wait.
    // The production code uses BV_HARD_TIMEOUT (10s); we test the same
    // channel pattern with a 200ms timeout.
    let test_timeout = std::time::Duration::from_millis(200);

    let (tx, rx) = std::sync::mpsc::channel::<TrustVcResult<AssertionOutcome>>();

    let assertion_name = "test_hard_bv_problem";

    std::thread::spawn(move || {
        // Simulate a solver that exceeds the timeout — sleep longer than
        // test_timeout without ever sending a result.
        std::thread::sleep(std::time::Duration::from_secs(2));
        // tx is dropped when the thread exits (after sleep), but the
        // receiver will have already timed out by then.
        let _ = tx;
    });

    // This matches the production timeout-handling pattern in assertion.rs.
    let result = match rx.recv_timeout(test_timeout) {
        Ok(result) => result,
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => Ok(AssertionOutcome::Unknown {
            reason: format!(
                "Solver timed out after {}s for '{}' (BV solver timeout enforcement, #1605)",
                BV_HARD_TIMEOUT.as_secs(),
                assertion_name
            ),
            category: Some(UnknownCategory::Timeout),
            detail: None,
        }),
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => Ok(AssertionOutcome::Unknown {
            reason: format!("Solver thread panicked (non-ay) for '{}'", assertion_name),
            category: Some(UnknownCategory::ThreadPanic),
            detail: None,
        }),
    };

    match result {
        Ok(AssertionOutcome::Unknown {
            reason, category, ..
        }) => {
            assert!(
                reason.contains("timed out"),
                "Expected timeout reason, got: {}",
                reason
            );
            assert!(
                reason.contains("BV solver timeout enforcement"),
                "Expected enforcement citation, got: {}",
                reason
            );
            assert!(
                reason.contains(assertion_name),
                "Expected assertion name in reason, got: {}",
                reason
            );
            assert_eq!(category, Some(UnknownCategory::Timeout));
        }
        other => panic!("Expected Unknown with timeout, got: {:?}", other),
    }
}

// ============================================================
// 2. RecvTimeoutError::Disconnected (non-ay thread panic)
// ============================================================

/// The channel Disconnected branch in verify_assertion_with_timeout_typed
/// fires when the solver thread panics with a non-ay panic. This test
/// exercises the exact production pattern:
///   catch_ay_sort_panics → resume_unwind (non-ay) → thread panic →
///   tx dropped → rx gets Disconnected
///
/// DISCRIMINATING: This test fails if:
/// - catch_ay_sort_panics starts catching non-ay panics
/// - The Disconnected arm is removed from the match
/// - resume_unwind is replaced with something that doesn't kill the thread
#[test]
fn test_non_ay_panic_causes_channel_disconnect() {
    use crate::encoder::verification::panic::catch_ay_sort_panics;
    use crate::encoder::verification::timeout::BV_HARD_TIMEOUT;

    let (tx, rx) = std::sync::mpsc::channel::<TrustVcResult<AssertionOutcome>>();

    std::thread::spawn(move || {
        // Exact production pattern from assertion.rs:
        // catch_ay_sort_panics wraps the solver call. Non-ay panics
        // are re-raised via resume_unwind, killing the thread and
        // dropping tx without sending.
        let result = catch_ay_sort_panics(std::panic::AssertUnwindSafe(|| {
            panic!("index out of bounds: the len is 3 but the index is 5");
        }));
        // This line is unreachable for non-ay panics — resume_unwind
        // unwinds the stack before we get here.
        let _ = tx.send(result);
    });

    // Match the production timeout-handling pattern from assertion.rs.
    match rx.recv_timeout(BV_HARD_TIMEOUT) {
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            // SUCCESS: non-ay panic propagated correctly through
            // catch_ay_sort_panics → resume_unwind → thread death →
            // channel disconnect
        }
        Ok(result) => panic!(
            "Non-ay panic should disconnect channel, but got result: {:?}",
            result
        ),
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => panic!(
            "Non-ay panic should disconnect within {}s (thread panics immediately)",
            BV_HARD_TIMEOUT.as_secs()
        ),
    }
    // Tautological VerifyResult format assertion removed by P1 audit —
    // it constructed its own string and asserted on it, testing nothing.
}

/// Complement test: ay panics are CAUGHT (not disconnected) — the thread
/// sends an `Unknown` outcome instead of dying. This ensures the ay/non-ay
/// bifurcation in catch_ay_sort_panics works correctly.
///
/// DISCRIMINATING: This test fails if catch_ay_sort_panics re-raises ay
/// panics (which would cause Disconnected instead of `Ok(Ok(Unknown))`).
#[test]
fn test_ay_panic_sends_result_not_disconnect() {
    use crate::encoder::verification::panic::catch_ay_sort_panics;
    use crate::encoder::verification::timeout::BV_HARD_TIMEOUT;

    let (tx, rx) = std::sync::mpsc::channel::<TrustVcResult<AssertionOutcome>>();

    std::thread::spawn(move || {
        let result = catch_ay_sort_panics(std::panic::AssertUnwindSafe(|| {
            panic!("sort mismatch: expected Bool, got BV(32)");
        }));
        // For ay panics, catch_ay_sort_panics returns Ok(Unknown)
        // instead of re-raising, so this send IS reached.
        let _ = tx.send(result);
    });

    match rx.recv_timeout(BV_HARD_TIMEOUT) {
        Ok(Ok(AssertionOutcome::Unknown {
            reason, category, ..
        })) => {
            assert!(
                reason.contains("ay solver panic"),
                "ay panic should be caught and reported, got: {}",
                reason
            );
            assert_eq!(category, Some(UnknownCategory::SolverPanic));
        }
        Ok(other) => panic!("Expected Unknown from ay panic, got: {:?}", other),
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            panic!("ay panic should NOT disconnect — catch_ay_sort_panics should catch it")
        }
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            panic!("ay panic handling should complete within timeout")
        }
    }
}

// ============================================================
// 3. Variable-divisor div-by-zero through full pipeline
// ============================================================

/// End-to-end test: x / y where y is unconstrained must produce a
/// division-by-zero counterexample when overflow checking is enabled.
///
/// Existing tests (int_mode_div_rem_overflow.rs) verify that the encoder
/// EMITS the div-by-zero overflow check predicate. This test verifies
/// the FULL PIPELINE: the overflow check is emitted, fed to the solver,
/// and the solver finds y == 0 as a counterexample.
///
/// DISCRIMINATING: This test fails if:
/// - The div-by-zero overflow check is not emitted
/// - The overflow check is emitted but not verified by the pipeline
/// - The verification loop in assertion.rs skips overflow checks
#[test]
fn test_variable_divisor_div_by_zero_pipeline() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 100"));
    // y is unconstrained — the solver can set y == 0
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "div_result",
        "x / y < 200",
    ));

    let result = AYEncoder::verify(&ctx);
    // The overflow checking loop in assertion.rs should catch y == 0
    // and return a Counterexample mentioning "division by zero".
    expect_fail_closed(
        &result,
        "x / y with unconstrained y should detect division by zero",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert!(
            obligation_name.contains("division by zero") || obligation_name.contains("div"),
            "Counterexample should mention division by zero, got: {}",
            obligation_name
        );
    }
}

/// Complement: x / y with y constrained to non-zero should verify.
///
/// DISCRIMINATING: This test fails if the div-by-zero guard rejects
/// ALL variable divisors (even when constrained away from zero).
#[test]
fn test_variable_divisor_nonzero_constrained_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(crate::vc::ProofObligation::assume("y_nonzero", "y == 5"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "div_result",
        "x / y == 20",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x / y with y == 5 should verify (no div-by-zero)");
}

/// Signed division: x / y with unconstrained y and signed overflow.
///
/// Tests that both the div-by-zero AND the signed MIN/-1 overflow
/// guards are exercised through the full pipeline.
#[test]
fn test_signed_variable_divisor_div_by_zero_pipeline() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // y is unconstrained — can be 0 (div-by-zero) or -1 with x=MIN (overflow)
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "div_result",
        "x / y == x / y",
    ));

    let result = AYEncoder::verify(&ctx);
    // Even a tautological assertion should fail due to overflow guards
    expect_fail_closed(
        &result,
        "Signed x / y with unconstrained y should detect div-by-zero or overflow",
    );
}

// ============================================================
// 4. Real ay sort mismatch through catch_ay_sort_panics
// ============================================================

/// Feed a REAL ay-dpll sort mismatch through catch_ay_sort_panics —
/// not a synthetic panic!("sort mismatch") but an actual ay API call
/// that triggers the internal sort check.
///
/// All existing tests in panic.rs use hardcoded panic!() strings. If
/// ay-dpll changes its panic message format, is_ay_panic could fail to
/// match. This test catches format drift by triggering a real panic.
///
/// DISCRIMINATING: This test fails if:
/// - ay-dpll changes SortMismatch Display format away from "sort mismatch"
/// - catch_ay_sort_panics stops catching the updated format
/// - `try_*().unwrap()` panic text stops matching the ay panic classifier
#[test]
fn test_real_ay_sort_mismatch_caught_by_catch_ay_sort_panics() {
    use crate::encoder::verification::panic::catch_ay_sort_panics;

    let result = catch_ay_sort_panics(std::panic::AssertUnwindSafe(|| {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        let bool_var = solver.declare_const("b", Sort::Bool);
        let bv_var = solver.declare_const("x", Sort::bitvec(32));

        // Trigger a REAL ay-dpll sort mismatch by passing a Bool
        // to a bitvector operation. `try_bvadd()` returns
        // SolverError::SortMismatch { operation: "try_bvadd", ... } and
        // unwrap() surfaces that as a panic message containing the sort
        // mismatch text that catch_ay_sort_panics classifies.
        let _term = solver.try_bvadd(bool_var, bv_var).unwrap();
        Ok(AssertionOutcome::Verified)
    }));

    match result {
        Ok(AssertionOutcome::Unknown {
            reason, category, ..
        }) => {
            assert!(
                reason.contains("ay solver panic"),
                "Should contain ay panic marker, got: {}",
                reason
            );
            assert!(
                reason.contains("sort mismatch") || reason.contains("SortMismatch"),
                "Should contain the real sort mismatch message, got: {}",
                reason
            );
            assert_eq!(category, Some(UnknownCategory::SolverPanic));
        }
        Ok(AssertionOutcome::Verified) => {
            panic!("bvadd(Bool, BV(32)) should panic with sort mismatch, not succeed")
        }
        Ok(AssertionOutcome::Counterexample { .. }) => {
            panic!("bvadd(Bool, BV(32)) should not produce a counterexample")
        }
        Ok(AssertionOutcome::Error { .. }) => {
            panic!("bvadd(Bool, BV(32)) should not produce a VIR-level error")
        }
        Err(other) => panic!("Expected Unknown from caught ay panic, got: {:?}", other),
    }
}

/// Same as above but with eq(Int, Bool) — another common sort mismatch
/// that can occur when the encoder passes wrong sorts to ay.
#[test]
fn test_real_ay_eq_sort_mismatch_caught() {
    use crate::encoder::verification::panic::catch_ay_sort_panics;

    let result = catch_ay_sort_panics(std::panic::AssertUnwindSafe(|| {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        let int_var = solver.declare_const("n", Sort::Int);
        let bool_var = solver.declare_const("b", Sort::Bool);

        // try_eq() on (Int, Bool) returns SortMismatch because the sorts
        // don't match. unwrap() turns that into the panic path we want.
        let _term = solver.try_eq(int_var, bool_var).unwrap();
        Ok(AssertionOutcome::Verified)
    }));

    // ay-dpll's try_eq() checks same-sort invariants and returns
    // SortMismatch; unwrap() panics, and catch_ay_sort_panics must catch it.
    match result {
        Ok(AssertionOutcome::Unknown {
            reason, category, ..
        }) => {
            assert!(
                reason.contains("ay solver panic"),
                "eq sort mismatch should be caught as ay panic, got: {}",
                reason
            );
            assert_eq!(category, Some(UnknownCategory::SolverPanic));
        }
        Ok(AssertionOutcome::Verified) => {
            panic!("eq(Int, Bool) should panic with sort mismatch, not succeed")
        }
        Ok(AssertionOutcome::Counterexample { .. }) => {
            panic!("eq(Int, Bool) should not produce a counterexample")
        }
        Ok(AssertionOutcome::Error { .. }) => {
            panic!("eq(Int, Bool) should not produce a VIR-level error")
        }
        Err(other) => panic!("Unexpected error variant: {:?}", other),
    }
}

// ============================================================
// 5. Interrupt handle — Phase 4 of #2242
// ============================================================

/// AYEncoder exposes the solver's interrupt handle via interrupt_handle().
/// When the caller stores `true`, the solver returns Unknown on the next
/// `check_sat_with_details()`. This is the mechanism that prevents orphaned
/// solver threads (#1703): on mpsc timeout, the handle is signaled so the
/// solver exits cleanly instead of running forever.
///
/// DISCRIMINATING: This test fails if:
/// - AYEncoder::interrupt_handle() is removed
/// - ay-dpll stops checking the interrupt flag during check_sat_with_details
/// - The interrupt handle is not the same Arc as the solver's internal flag
#[test]
fn test_interrupt_handle_causes_unknown() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver.declare_const("x", Sort::bitvec(32));
    let zero = encoder.solver.try_bv_const(0, 32).unwrap();
    let eq = encoder.solver.try_eq(x, zero).unwrap();
    encoder.solver.try_assert_term(eq).unwrap();

    // Get the interrupt handle and signal it BEFORE check_sat_with_details
    let handle = encoder.interrupt_handle();
    handle.store(true, std::sync::atomic::Ordering::Relaxed);

    let details = encoder.solver.check_sat_with_details();
    assert!(
        details.result.is_unknown(),
        "Interrupted solver should return Unknown, got: {:?}",
        details.result.result()
    );
    assert_eq!(
        details.unknown_reason,
        Some(UnknownReason::Interrupted),
        "Interrupted solve should preserve structured UnknownReason"
    );

    // Clear the interrupt and verify normal solving resumes
    handle.store(false, std::sync::atomic::Ordering::Relaxed);
    let details2 = encoder.solver.check_sat_with_details();
    assert!(
        details2.result.is_sat(),
        "After clearing interrupt, solver should return Sat, got: {:?}",
        details2.result.result()
    );
}

/// Verify that a real ay operation that does NOT mismatch sorts is
/// NOT caught by catch_ay_sort_panics — it returns the inner result.
///
/// Control test ensuring catch_ay_sort_panics is transparent for
/// non-panicking operations.
#[test]
fn test_real_ay_valid_operation_passes_through() {
    use crate::encoder::verification::panic::catch_ay_sort_panics;

    let result = catch_ay_sort_panics(std::panic::AssertUnwindSafe(|| {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        let x = solver.declare_const("x", Sort::bitvec(32));
        let y = solver.declare_const("y", Sort::bitvec(32));

        // Valid operation: try_bvadd(BV(32), BV(32)) → BV(32)
        let sum = solver.try_bvadd(x, y).unwrap();
        // Verify the result is usable
        let zero = solver.try_bv_const(0, 32).unwrap();
        let eq_term = solver.try_eq(sum, zero).unwrap();
        solver.try_assert_term(eq_term).unwrap();
        let sat_result = solver.try_check_sat().unwrap();
        assert!(
            sat_result.is_sat(),
            "expected valid BV add to remain satisfiable"
        );
        Ok(AssertionOutcome::Verified)
    }));

    match result {
        Ok(AssertionOutcome::Verified) => { /* Expected: valid operation passes through */ }
        Ok(other) => panic!("Expected Verified for valid BV add, got: {:?}", other),
        Err(e) => panic!("Valid BV add should not trigger any error: {:?}", e),
    }
}
