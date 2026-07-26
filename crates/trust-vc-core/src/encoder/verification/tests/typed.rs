//! Typed verification regression tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Tests the `verify_typed` dispatch logic in `typed.rs`, focusing on paths
//! not covered by encoder integration tests:
//! - LoopEnsures with guard negation
//! - InvariantExceptBreak vs LoopInvariant filtering
//! - AssertBy scope resolution
//! - Edge cases in obligation routing

use crate::encoder::tests::expect_verified;
use crate::encoder::tests::ForcedFlagGuard;
use crate::encoder::types::VerifyResult;
use crate::encoder::verification::test_hooks::{
    per_assertion_prune_plan_build_count, reset_per_assertion_prune_plan_build_count,
    reset_setup_from_prepared_count, reset_shared_bv_reuse_attempt_count,
    setup_from_prepared_count, shared_bv_reuse_attempt_count, FORCE_BV_TIMEOUT,
};
use crate::encoder::AYEncoder;
use crate::ir::TrustVcType;
use crate::prepared_context::prepare_context;
use crate::vc::{ProofObligation, VerificationContext};

#[test]
fn test_verify_typed_seq_push_exists_no_longer_reports_setup_unknown() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "s",
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    ctx.push_obligation(ProofObligation::assume(
        "exists_push_assume",
        "exists(|v: i32| s.push(v).len() == 3)",
    ));
    ctx.push_obligation(ProofObligation::assert("trivial_assert", "true"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let result = AYEncoder::verify_typed(&prepared);

    expect_verified(
        &result,
        "typed setup should verify once the old Seq push sort-mismatch path is fixed",
    );
}

#[test]
fn test_regular_assertions_share_single_bv_setup() {
    reset_setup_from_prepared_count();
    reset_shared_bv_reuse_attempt_count();

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("self_eq", "x == x"));
    ctx.push_obligation(ProofObligation::assert("self_ge", "x >= x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "two regular assertions should verify through the shared BV fast path",
    );
    assert_eq!(
        setup_from_prepared_count(),
        1,
        "regular assertions should build one shared BV encoder",
    );
    assert_eq!(
        shared_bv_reuse_attempt_count(),
        2,
        "shared BV fast path should be attempted once per regular assertion",
    );

    reset_setup_from_prepared_count();
    reset_shared_bv_reuse_attempt_count();
}

#[test]
fn test_regular_assertions_abandon_shared_encoder_after_timeout() {
    reset_setup_from_prepared_count();
    reset_per_assertion_prune_plan_build_count();
    reset_shared_bv_reuse_attempt_count();

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Uint { width: 64 });
    ctx.push_obligation(ProofObligation::assert("self_eq", "x == x"));
    ctx.push_obligation(ProofObligation::assert("self_ge", "x >= x"));

    let result = {
        let _timeout = ForcedFlagGuard::new(&FORCE_BV_TIMEOUT);
        AYEncoder::verify(&ctx)
    };

    expect_verified(
        &result,
        "forced timeout should abandon shared reuse and recover through the fresh retry path",
    );
    assert_eq!(
        shared_bv_reuse_attempt_count(),
        1,
        "shared BV reuse must stop after the first timeout",
    );
    assert_eq!(
        setup_from_prepared_count(),
        5,
        "one shared setup plus two fresh retry setups per assertion should remain after abandonment",
    );
    assert_eq!(
        per_assertion_prune_plan_build_count(),
        2,
        "each fresh fallback assertion should build its per-assertion prune plan once and reuse it across retry stages",
    );

    reset_setup_from_prepared_count();
    reset_per_assertion_prune_plan_build_count();
    reset_shared_bv_reuse_attempt_count();
}

#[test]
fn test_collection_confirmation_reuses_per_assertion_prune_plan() {
    reset_setup_from_prepared_count();
    reset_per_assertion_prune_plan_build_count();

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.obligations.push(ProofObligation::measure_non_negative(
        "len_nonneg",
        "s.len() >= 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collection measure should verify through overflow, main, and confirmation passes",
    );
    assert_eq!(
        setup_from_prepared_count(),
        3,
        "collection measure should build overflow, main, and confirmation encoders",
    );
    assert_eq!(
        per_assertion_prune_plan_build_count(),
        1,
        "overflow, main, and confirmation should reuse one per-assertion prune plan",
    );

    reset_setup_from_prepared_count();
    reset_per_assertion_prune_plan_build_count();
}

#[test]
fn test_collection_assertions_skip_shared_bv_fast_path() {
    reset_setup_from_prepared_count();
    reset_shared_bv_reuse_attempt_count();

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert(
        "view_set",
        "s.view().contains(x) == s.contains(x)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collection assertions should verify on fresh encoders, not the shared BV fast path",
    );
    assert_eq!(
        shared_bv_reuse_attempt_count(),
        0,
        "collection assertions must bypass shared BV reuse to avoid nested confirmation stack blowups",
    );

    reset_setup_from_prepared_count();
    reset_shared_bv_reuse_attempt_count();
}

#[test]
fn test_collection_context_disables_shared_bv_fast_path_for_scalar_assertions() {
    reset_setup_from_prepared_count();
    reset_shared_bv_reuse_attempt_count();

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("len_nonneg", "s.len() >= 0"));
    ctx.push_obligation(ProofObligation::assert("x_self_eq", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mixed collection contexts should also bypass shared BV reuse",
    );
    assert_eq!(
        shared_bv_reuse_attempt_count(),
        0,
        "collection-aware contexts must not enter the shared BV fast path",
    );

    reset_setup_from_prepared_count();
    reset_shared_bv_reuse_attempt_count();
}

// ========================================================================
// LoopEnsures — verify_typed lines 206-242
// ========================================================================

/// LoopEnsures with a single guard: the verifier assumes ¬guard after the loop.
///
/// Setup: `count` (modified), `limit` (unmodified).
/// Invariant: `limit == 10` on unmodified var — inductive via frame condition.
/// Guard: `count < limit`.
/// After the loop: ¬(count < limit) → count >= limit → count >= 10.
/// LoopEnsures: `count >= 10`.
///
/// Exercises the normal_exit_guard construction at typed.rs:211-225 and
/// the LoopEnsures verification at typed.rs:230-242.
#[test]
fn test_loop_ensures_with_guard_negation_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("count", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("limit", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_count", "count == 0"));
    ctx.push_obligation(ProofObligation::assume("init_limit", "limit == 10"));
    // Invariant on unmodified variable — inductive via frame condition.
    ctx.obligations.push(ProofObligation::loop_invariant(
        "limit_stable",
        "limit == 10",
    ));
    ctx.set_loop_modified_vars("limit_stable", vec!["count".to_string()]);
    ctx.obligations
        .push(ProofObligation::loop_guard("loop_guard", "count < limit"));
    // After loop: ¬(count < limit) ∧ limit==10 → count >= 10
    ctx.obligations.push(ProofObligation::loop_ensures(
        "ensures_count_ge_10",
        "count >= 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "loop_ensures count>=10 with guard ¬(count<limit) should verify",
    );
}

/// LoopEnsures without a loop guard: only invariants are available.
///
/// Without a guard, there is no ¬guard assumption. The ensures must hold
/// from the invariant alone.
///
/// Invariant: `y == 5` on unmodified var; ensures: `y == 5`.
#[test]
fn test_loop_ensures_without_guard_uses_invariant_only() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 5"));
    // Invariant on unmodified variable — inductive via frame condition.
    ctx.obligations
        .push(ProofObligation::loop_invariant("y_stable", "y == 5"));
    ctx.set_loop_modified_vars("y_stable", vec!["x".to_string()]);
    // No loop guard
    ctx.obligations
        .push(ProofObligation::loop_ensures("ensures_y_5", "y == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "loop_ensures y==5 from invariant alone should verify",
    );
}

/// LoopEnsures that requires the guard negation to hold — fails without guard.
///
/// Invariant: `limit == 10` on unmodified var; ensures: `count >= 10`.
/// Without a guard providing ¬(count<limit), count >= 10 cannot be proven
/// since count is havoced.
///
/// Discriminating pair with test_loop_ensures_with_guard_negation_verifies.
#[test]
fn test_loop_ensures_needing_guard_fails_without_guard() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("count", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("limit", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_count", "count == 0"));
    ctx.push_obligation(ProofObligation::assume("init_limit", "limit == 10"));
    ctx.obligations.push(ProofObligation::loop_invariant(
        "limit_stable",
        "limit == 10",
    ));
    ctx.set_loop_modified_vars("limit_stable", vec!["count".to_string()]);
    // No loop guard — count >= 10 cannot be proven from limit==10 alone
    ctx.obligations.push(ProofObligation::loop_ensures(
        "ensures_count_ge_10",
        "count >= 10",
    ));

    let result = AYEncoder::verify(&ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "loop_ensures count>=10 without guard should NOT verify: {:?}",
        result
    );
}

// ========================================================================
// InvariantExceptBreak filtering — verify_typed lines 196-204
// ========================================================================

/// InvariantExceptBreak obligations are verified (base + inductive step)
/// just like LoopInvariant obligations, but are filtered from
/// `always_available_invariants` at typed.rs:200-204.
///
/// This test verifies that IEB obligations undergo the full verification
/// cycle (both base case and inductive step succeed).
#[test]
fn test_invariant_except_break_is_verified_like_loop_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 5"));
    // IEB invariant on y: y is unmodified, so frame condition preserves it.
    ctx.obligations
        .push(ProofObligation::invariant_except_break("ieb_y_5", "y == 5"));
    ctx.set_loop_modified_vars("ieb_y_5", vec!["x".to_string()]);
    // Need at least one assertion for the context to be valid
    ctx.push_obligation(ProofObligation::assert("trivial", "true"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "IEB invariant on unmodified var should verify (base + inductive step)",
    );
}

/// LoopInvariant IS available to regular assertions (positive companion).
///
/// Invariant: `y == 5`. Post-loop assertion: `y == 5`.
/// LoopInvariant facts are in always_available_invariants → assertion sees them.
#[test]
fn test_loop_invariant_available_to_regular_assertions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 5"));
    ctx.obligations
        .push(ProofObligation::loop_invariant("y_stable", "y == 5"));
    ctx.set_loop_modified_vars("y_stable", vec!["x".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post_y", "y == 5"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "LoopInvariant y==5 should be available to post-loop assertion",
    );
}

/// LoopEnsures sees ALL verified invariants (both LoopInvariant and IEB).
///
/// This is the critical distinction: LoopEnsures uses `verified_invariant_obligations`
/// (all invariants), while regular assertions use `always_available_invariants`
/// (LoopInvariant only). Part of typed.rs:235 vs typed.rs:332.
///
/// Setup: IEB invariant `y == 7` on unmodified var (inductive via frame).
/// LoopEnsures checks `y == 7`. Should verify because LoopEnsures sees ALL invariants.
#[test]
fn test_loop_ensures_sees_all_invariants_including_ieb() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 7"));
    // IEB invariant on unmodified y — inductive via frame condition.
    ctx.obligations
        .push(ProofObligation::invariant_except_break("ieb_y_7", "y == 7"));
    ctx.set_loop_modified_vars("ieb_y_7", vec!["x".to_string()]);
    // LoopEnsures sees all invariants including IEB → should verify.
    ctx.obligations
        .push(ProofObligation::loop_ensures("ensures_y_7", "y == 7"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LoopEnsures should see IEB invariants");
}

/// InvariantExceptBreak is NOT available to regular post-loop assertions.
///
/// Negative companion to test_loop_ensures_sees_all_invariants_including_ieb.
///
/// Setup: x, y, z. LoopInvariant `z > 0` modifies {x, y}. IEB `y == 7` modifies {x}.
/// The union of modified vars is {x, y} — so `y` is havocked in the post-loop frame.
///
/// The IEB itself verifies: base case from `init_y`, inductive step from frame
/// condition (y unmodified per IEB's own modified_vars). But:
/// - IEB is filtered from `always_available_invariants` (typed.rs:199-207)
/// - `y` is in the union of modified vars → havocked → entry assumption forgotten
///
/// Both mechanisms combine: the regular assertion `y == 7` cannot be proven.
/// Part of #2448.
#[test]
fn test_invariant_except_break_not_available_to_regular_assertion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("z", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_x", "x == 0"));
    ctx.push_obligation(ProofObligation::assume("init_y", "y == 7"));
    ctx.push_obligation(ProofObligation::assume("init_z", "z == 1"));
    // LoopInvariant on z modifies {x, y} — y enters the union of modified vars.
    ctx.obligations
        .push(ProofObligation::loop_invariant("inv_z_pos", "z > 0"));
    ctx.set_loop_modified_vars("inv_z_pos", vec!["x".to_string(), "y".to_string()]);
    // IEB on y modifies only {x} — y is unmodified per IEB, so inductive step
    // succeeds via frame condition. But IEB is excluded from always_available.
    ctx.obligations
        .push(ProofObligation::invariant_except_break("ieb_y_7", "y == 7"));
    ctx.set_loop_modified_vars("ieb_y_7", vec!["x".to_string()]);
    // Regular assertion: y == 7. Not provable because (a) IEB filtered from
    // always_available_invariants, (b) y is havocked in post-loop frame.
    ctx.push_obligation(ProofObligation::assert("post_y_7", "y == 7"));

    let result = AYEncoder::verify(&ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Regular assertion should NOT see IEB invariant facts: {:?}",
        result
    );
}

// ========================================================================
// AssertBy scope resolution — verify_typed lines 244-275
// ========================================================================

/// AssertBy with a properly registered scope verifies the scoped proof.
///
/// Exercises the assert_by_scopes lookup at typed.rs:247-262.
#[test]
fn test_assert_by_with_scope_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init", "x == 42"));

    // The assert_by obligation says x > 0; the scope provides x == 42 as
    // additional evidence.
    ctx.add_assert_by(
        "by_block",
        "x > 0",
        vec![ProofObligation::assume("scope_assume", "x == 42")],
    );

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "assert_by with scope x==42 proving x>0 should verify",
    );
}

// ========================================================================
// Edge: Reveal obligations — verify_typed line 57
// ========================================================================

/// Reveal obligations are metadata — they should not be classified as
/// assumptions or assertions. verify_typed skips them (line 57).
#[test]
fn test_reveal_obligation_is_metadata_only() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("check", "x == 1"));
    // Register the function so reveal validation passes (#2473).
    ctx.declare_helper_function_typed("some_fn", TrustVcType::Int { width: 32 }, vec![]);
    // Add a reveal — it shouldn't affect the verification outcome.
    ctx.obligations.push(ProofObligation::reveal("some_fn"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Reveal obligation should not affect verification");
}

// ========================================================================
// Measure obligations — verify_typed lines 62-63
// ========================================================================

/// MeasureNonNegative: a simple non-negative measure check verifies when
/// the measure expression is provably >= 0.
///
/// Setup: `n` (u32) with `n == 5`.
/// MeasureNonNegative: `n >= 0` (trivially true for u32 >= 0 under assumptions).
///
/// Exercises the MeasureNonNegative → assertions partition at typed.rs:62.
#[test]
fn test_measure_non_negative_verifies_with_valid_assumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_n", "n == 5"));
    ctx.obligations
        .push(ProofObligation::measure_non_negative("n_nonneg", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MeasureNonNegative n>=0 with n==5 should verify");
}

/// MeasureDecreases: a decreases check verifies when old > new under assumptions.
///
/// Setup: `n_old` and `n_new` (u32) with `n_old == 5` and `n_new == 4`.
/// MeasureDecreases: `n_old > n_new` (5 > 4 = true).
///
/// Exercises the MeasureDecreases → assertions partition at typed.rs:63.
#[test]
fn test_measure_decreases_verifies_with_valid_assumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n_old", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("n_new", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_old", "n_old == 5"));
    ctx.push_obligation(ProofObligation::assume("init_new", "n_new == 4"));
    ctx.obligations
        .push(ProofObligation::measure_decreases("n_dec", "n_old > n_new"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "MeasureDecreases n_old>n_new with 5>4 should verify",
    );
}

/// MeasureDecreases that fails: `n_old == n_new` should NOT verify as decreasing.
///
/// Discriminating pair with test_measure_decreases_verifies_with_valid_assumption.
#[test]
fn test_measure_decreases_fails_when_not_decreasing() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n_old", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("n_new", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_old", "n_old == 5"));
    ctx.push_obligation(ProofObligation::assume("init_new", "n_new == 5"));
    ctx.obligations
        .push(ProofObligation::measure_decreases("n_dec", "n_old > n_new"));

    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample {
                ref obligation_name,
                ..
            } if obligation_name == "n_dec"
        ),
        "MeasureDecreases with equal values should produce a counterexample for n_dec: {:?}",
        result
    );
}

/// MeasureNonNegative that fails: an unconstrained i32 can be negative,
/// so `n >= 0` is not provable.
///
/// Discriminating pair with test_measure_non_negative_verifies_with_valid_assumption.
/// Without this, the positive test could pass trivially (u32 >= 0 is always true).
#[test]
fn test_measure_non_negative_fails_when_unconstrained_signed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::Int { width: 32 });
    // No assumption constraining n — it can be any i32 including negatives.
    ctx.obligations
        .push(ProofObligation::measure_non_negative("n_nonneg", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample {
                ref obligation_name,
                ..
            } if obligation_name == "n_nonneg"
        ),
        "MeasureNonNegative n>=0 with unconstrained i32 should produce a counterexample for n_nonneg: {:?}",
        result
    );
}

// ========================================================================
// Bounded shared-BV reuse — #2544
// ========================================================================

/// 20 trivial scalar assertions verify successfully with bounded encoder
/// reuse. The shared-BV encoder is rebuilt every SHARED_BV_REUSE_BATCH_LIMIT
/// assertions (8) to prevent ay-dpll incremental state accumulation from
/// degrading BV decompose performance.
///
/// With batch limit 8 and 20 assertions: 3 encoder setups (1-8, 9-16, 17-20).
#[test]
fn test_regular_assertions_bounded_reuse_20_assertions() {
    reset_setup_from_prepared_count();
    reset_shared_bv_reuse_attempt_count();

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("bound", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("bound2", "y > 0"));

    for i in 0..20 {
        ctx.push_obligation(ProofObligation::assert(
            format!("identity_{}", i),
            "x + 0 == x",
        ));
    }

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "20 trivial assertions should verify with bounded BV reuse",
    );

    let setups = setup_from_prepared_count();
    assert!(
        setups > 1 && setups < 20,
        "Expected 3 encoder setups for 20 assertions with batch limit 8, got {}",
        setups,
    );
    assert_eq!(
        shared_bv_reuse_attempt_count(),
        20,
        "shared BV fast path should be attempted for all 20 assertions",
    );

    reset_setup_from_prepared_count();
    reset_shared_bv_reuse_attempt_count();
}

/// Both MeasureNonNegative and MeasureDecreases in the same context
/// (typical pattern for a recursive function with `#[decreases(n)]`).
///
/// Exercises that both measure kinds are routed to the assertions vector
/// and verified together.
#[test]
fn test_measure_nonneg_and_decreases_combined() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 32 });
    ctx.declare_var_typed("n_rec", TrustVcType::Uint { width: 32 });
    ctx.push_obligation(ProofObligation::assume("init_n", "n == 5"));
    ctx.push_obligation(ProofObligation::assume("init_rec", "n_rec == 4"));
    // Non-negative: measure >= 0
    ctx.obligations
        .push(ProofObligation::measure_non_negative("n_nonneg", "n >= 0"));
    // Decreases: old > new
    ctx.obligations
        .push(ProofObligation::measure_decreases("n_dec", "n > n_rec"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Combined nonneg + decreases should verify");
}
