//! Incremental encoder reuse tests — shared solver context via push/pop.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verifies that `verify_assertion_typed()` can be called multiple times on
//! the same encoder with `reset_flush_state()` between calls, confirming
//! that ground axioms are correctly re-flushed for each assertion.
//!
//! Part of #2496.

use super::*;
use crate::encoder::verification::assertion_timeout::{
    verify_assertion_with_timeout_reuse, ReuseAttempt,
};
use crate::encoder::verification::outcome::AssertionOutcome;
use crate::encoder::verification::test_hooks::FORCE_SCOPE_POP_FAILURE_ONCE;
use crate::prepared_context::{prepare_context, PreparedObligation};
use crate::vc::{ObligationKind, OverflowBehavior};

/// Regression: call `verify_assertion_with_timeout_reuse` twice on the same
/// encoder, confirming the second call still verifies correctly after ground
/// pool flush state is reset.
///
/// Setup: x: i32, assume x > 0.
/// Assertion 1: x > 0 (trivially true from assumption)
/// Assertion 2: x >= 1 (follows from x > 0 on signed integers)
///
/// Without `reset_flush_state()` between calls, the second call's ground
/// axiom instantiations would be silently skipped (stale `instantiated_pairs`).
/// This test does not use collection types (no ground pool activity), so it
/// validates the basic reuse path. The collection-involving variant is below.
#[test]
fn test_encoder_reuse_two_assertions_both_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("a1", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("a2", "x >= 1"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    let assumptions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume))
        .collect();
    let assertions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert))
        .collect();
    assert_eq!(assertions.len(), 2, "should have exactly 2 assertions");

    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &assumptions,
        &[],
        &[],
        &[],
        &[],
    );
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    // First assertion
    let attempt1 = verify_assertion_with_timeout_reuse(encoder, assertions[0], None)
        .expect("attempt1 should work");
    let mut encoder = match attempt1 {
        ReuseAttempt::Completed { encoder, outcome } => {
            assert!(
                matches!(outcome, AssertionOutcome::Verified),
                "first assertion (x > 0) should verify: {:?}",
                outcome
            );
            encoder
        }
        ReuseAttempt::TimedOut => panic!("first assertion should not time out"),
        ReuseAttempt::NonReusable { outcome } => panic!(
            "first assertion should remain reusable, got NonReusable: {:?}",
            outcome
        ),
        ReuseAttempt::Panicked { .. } => panic!("first assertion should not panic"),
    };

    // Reset ground pool state between assertions
    encoder.state.ground_pool.reset_flush_state();

    // Second assertion on the SAME encoder
    let attempt2 = verify_assertion_with_timeout_reuse(encoder, assertions[1], None)
        .expect("attempt2 should work");
    match attempt2 {
        ReuseAttempt::Completed { outcome, .. } => {
            assert!(
                matches!(outcome, AssertionOutcome::Verified),
                "second assertion (x >= 1) should verify on reused encoder: {:?}",
                outcome
            );
        }
        ReuseAttempt::TimedOut => panic!("second assertion should not time out"),
        ReuseAttempt::NonReusable { outcome } => panic!(
            "second assertion should remain reusable, got NonReusable: {:?}",
            outcome
        ),
        ReuseAttempt::Panicked { .. } => panic!("second assertion should not panic"),
    };
}

/// Encoder reuse with a collection context: ground pool flush state matters.
///
/// Setup: s: Seq<i32>, assume s.len() >= 2, broadcast forall j: s.index(j) >= 0
/// Assertion 1: s.index(0) >= 0
/// Assertion 2: s.index(1) >= 0
///
/// Both assertions require the broadcast to be instantiated for specific index
/// values. After the first assertion's push/pop cycle, `instantiated_pairs` marks
/// the (axiom, args) as done. Without `reset_flush_state()`, the second assertion
/// would NOT see the ground axiom instances (they were retracted by pop).
#[test]
fn test_encoder_reuse_collection_context_ground_pool_reflushed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("j", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.push_obligation(ProofObligation::assume("len_bound", "s.len() >= 2"));

    // Broadcast: non-negative elements with trigger on s.index(j)
    let broadcast = ProofObligation::broadcast_assume("nonneg", "s.index(j) >= 0")
        .with_bound_vars(vec!["j".to_string()])
        .with_trigger_patterns(vec![vec!["s.index(j)".to_string()]]);
    ctx.obligations.push(broadcast);

    ctx.push_obligation(ProofObligation::assert("elem0_nonneg", "s.index(0) >= 0"));
    ctx.push_obligation(ProofObligation::assert("elem1_nonneg", "s.index(1) >= 0"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    let assumptions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume))
        .collect();
    let broadcasts: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::BroadcastAssume))
        .collect();
    let assertions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert))
        .collect();
    assert_eq!(assertions.len(), 2, "should have exactly 2 assertions");

    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &assumptions,
        &broadcasts,
        &[],
        &[],
        &[],
    );
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    // First assertion: s.index(0) >= 0
    let attempt1 = verify_assertion_with_timeout_reuse(encoder, assertions[0], None)
        .expect("attempt1 should work");
    let mut encoder = match attempt1 {
        ReuseAttempt::Completed { encoder, outcome } => {
            assert!(
                matches!(outcome, AssertionOutcome::Verified),
                "s.index(0) >= 0 should verify: {:?}",
                outcome
            );
            encoder
        }
        ReuseAttempt::TimedOut => panic!("first assertion should not time out"),
        ReuseAttempt::NonReusable { outcome } => panic!(
            "first assertion should remain reusable, got NonReusable: {:?}",
            outcome
        ),
        ReuseAttempt::Panicked { .. } => panic!("first assertion should not panic"),
    };

    // Critical: reset ground pool flush state so axioms are re-flushed
    encoder.state.ground_pool.reset_flush_state();

    // Second assertion on the SAME encoder: s.index(1) >= 0
    let attempt2 = verify_assertion_with_timeout_reuse(encoder, assertions[1], None)
        .expect("attempt2 should work");
    match attempt2 {
        ReuseAttempt::Completed { outcome, .. } => {
            assert!(
                matches!(outcome, AssertionOutcome::Verified),
                "s.index(1) >= 0 should verify on reused encoder with reset_flush_state: {:?}",
                outcome
            );
        }
        ReuseAttempt::TimedOut => panic!("second assertion should not time out"),
        ReuseAttempt::NonReusable { outcome } => panic!(
            "second assertion should remain reusable, got NonReusable: {:?}",
            outcome
        ),
        ReuseAttempt::Panicked { .. } => panic!("second assertion should not panic"),
    };
}

/// Verify that the second assertion on a reused encoder correctly detects a
/// counterexample (not just always reporting Verified).
///
/// Setup: x: i32, assume x > 0.
/// Assertion 1: x > 0 (verified)
/// Assertion 2: x > 100 (counterexample: x = 1)
///
/// Ensures the reuse path preserves counterexample detection — not all
/// assertions trivially verify after push/pop.
#[test]
fn test_encoder_reuse_second_assertion_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("a1", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("a2", "x > 100"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    let assumptions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume))
        .collect();
    let assertions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert))
        .collect();
    assert_eq!(assertions.len(), 2);

    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &assumptions,
        &[],
        &[],
        &[],
        &[],
    );
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    // First assertion: x > 0 (verifies)
    let attempt1 = verify_assertion_with_timeout_reuse(encoder, assertions[0], None)
        .expect("attempt1 should work");
    let mut encoder = match attempt1 {
        ReuseAttempt::Completed { encoder, outcome } => {
            assert!(
                matches!(outcome, AssertionOutcome::Verified),
                "x > 0 should verify: {:?}",
                outcome
            );
            encoder
        }
        other => panic!(
            "first assertion unexpected: {:?}",
            std::mem::discriminant(&other)
        ),
    };

    encoder.state.ground_pool.reset_flush_state();

    // Second assertion: x > 100 (should be counterexample)
    let attempt2 = verify_assertion_with_timeout_reuse(encoder, assertions[1], None)
        .expect("attempt2 should work");
    match attempt2 {
        ReuseAttempt::Completed { outcome, .. } => {
            assert!(
                matches!(outcome, AssertionOutcome::Counterexample { .. }),
                "x > 100 should be counterexample on reused encoder: {:?}",
                outcome
            );
        }
        other => panic!(
            "second assertion unexpected: {:?}",
            std::mem::discriminant(&other)
        ),
    };
}

/// Overflow assumptions for reused BV assertions must live only inside the
/// pushed solver frame. Otherwise each assertion permanently grows the base
/// solver state and later checks inherit stale "no overflow" facts. Part of
/// #2552.
#[test]
fn test_reused_encoder_does_not_accumulate_overflow_assumptions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.set_overflow_behavior(OverflowBehavior::Error);
    ctx.push_obligation(ProofObligation::assume("x_small", "x < 10"));
    ctx.push_obligation(ProofObligation::assert("a1", "x + 1 > x"));
    ctx.push_obligation(ProofObligation::assert("a2", "x + 2 > x"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let assumptions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume))
        .collect();
    let assertions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assert))
        .collect();
    assert_eq!(assertions.len(), 2, "should have exactly 2 assertions");

    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &assumptions,
        &[],
        &[],
        &[],
        &[],
    );
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");
    let baseline_assertions = encoder.solver.assertions().len();

    let attempt1 = verify_assertion_with_timeout_reuse(encoder, assertions[0], None)
        .expect("attempt1 should work");
    let mut encoder = match attempt1 {
        ReuseAttempt::Completed { encoder, outcome } => {
            assert!(
                matches!(outcome, AssertionOutcome::Verified),
                "first overflow-checked assertion should verify: {:?}",
                outcome
            );
            assert_eq!(
                encoder.solver.assertions().len(),
                baseline_assertions,
                "overflow assumptions from the first assertion must not leak into the base solver"
            );
            encoder
        }
        ReuseAttempt::TimedOut => panic!("first assertion should not time out"),
        ReuseAttempt::NonReusable { outcome } => panic!(
            "first assertion should remain reusable, got NonReusable: {:?}",
            outcome
        ),
        ReuseAttempt::Panicked { outcome } => {
            panic!("first assertion should not panic: {:?}", outcome)
        }
    };

    encoder.state.ground_pool.reset_flush_state();

    let attempt2 = verify_assertion_with_timeout_reuse(encoder, assertions[1], None)
        .expect("attempt2 should work");
    match attempt2 {
        ReuseAttempt::Completed { encoder, outcome } => {
            assert!(
                matches!(outcome, AssertionOutcome::Verified),
                "second overflow-checked assertion should verify: {:?}",
                outcome
            );
            assert_eq!(
                encoder.solver.assertions().len(),
                baseline_assertions,
                "overflow assumptions from the second assertion must not leak into the base solver"
            );
        }
        ReuseAttempt::TimedOut => panic!("second assertion should not time out"),
        ReuseAttempt::NonReusable { outcome } => panic!(
            "second assertion should remain reusable, got NonReusable: {:?}",
            outcome
        ),
        ReuseAttempt::Panicked { outcome } => {
            panic!("second assertion should not panic: {:?}", outcome)
        }
    }
}

#[test]
fn test_scope_pop_failure_marks_encoder_non_reusable() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("a1", "x > 0"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let assumptions: Vec<&PreparedObligation> = prepared
        .obligations
        .iter()
        .filter(|o| matches!(o.kind, ObligationKind::Assume))
        .collect();
    let assertion = prepared
        .obligations
        .iter()
        .find(|o| matches!(o.kind, ObligationKind::Assert))
        .expect("assertion should exist");

    let slices = crate::encoder::verification::VerificationSlices::new(
        &prepared,
        &assumptions,
        &[],
        &[],
        &[],
        &[],
    );
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    FORCE_SCOPE_POP_FAILURE_ONCE.with(|flag| flag.set(true));
    let attempt =
        verify_assertion_with_timeout_reuse(encoder, assertion, None).expect("attempt should work");

    match attempt {
        ReuseAttempt::NonReusable { outcome } => {
            assert!(
                matches!(outcome, AssertionOutcome::Verified),
                "scope-pop failures should preserve the completed assertion outcome: {:?}",
                outcome
            );
        }
        ReuseAttempt::Completed { outcome, .. } => panic!(
            "forced scope-pop failure must drop encoder reuse, got Completed: {:?}",
            outcome
        ),
        ReuseAttempt::TimedOut => panic!("forced scope-pop failure should not time out"),
        ReuseAttempt::Panicked { outcome } => {
            panic!(
                "forced scope-pop failure should not be classified as panic: {:?}",
                outcome
            )
        }
    }
}
