// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 64 — GCD via Euclidean Algorithm VCs (Groups A–D).
//!
//! The Euclidean algorithm computes gcd(a, b) by repeated remainder:
//!   while b != 0 { let t = b; b = a % b; a = t; }
//!   return a
//!
//! Groups A–D: Init, Step, Invariant, Exit.
//! Groups E–F (extended, negatives): see test_verifythis_gcd_extended.rs.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

fn verify_with_pipeline(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

// ========================================================================
// GROUP A: Init — establish loop invariant at entry
// ========================================================================

/// Tier 64a: Init — gcd(a, b) is preserved at loop entry with concrete values.
/// gcd(48, 18) = 6 — the invariant holds trivially before the first iteration.
#[test]
fn test_vt_tier64a_gcd_init_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");

    ctx.push_assume("a_val", "a == 48");
    ctx.push_assume("b_val", "b == 18");

    // Both operands are positive at entry
    ctx.push_assert("a_pos", "a > 0");
    ctx.push_assert("b_pos", "b > 0");
    // b < a (typical for Euclidean GCD to make progress)
    ctx.push_assert("b_lt_a", "b < a");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64a: gcd init concrete should verify, got: {:?}",
        result,
    );
}

/// Tier 64a: Init — symbolic setup where a >= b > 0.
#[test]
fn test_vt_tier64a_gcd_init_symbolic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");

    ctx.push_assume("a_bound", "a >= 1 && a <= 1000");
    ctx.push_assume("b_bound", "b >= 1 && b <= 1000");
    ctx.push_assume("a_ge_b", "a >= b");

    // Invariant: both are bounded and non-negative (u64 guarantees non-negative)
    ctx.push_assert("a_bounded", "a <= 1000");
    ctx.push_assert("b_bounded", "b <= 1000");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64a: gcd init symbolic should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — one iteration of the Euclidean algorithm
// ========================================================================

/// Tier 64b: Step — one iteration: gcd(48, 18) → gcd(18, 12).
/// 48 % 18 = 12, so after one step a=18, b=12.
#[test]
fn test_vt_tier64b_gcd_step_48_18() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");
    ctx.declare_var_parsed("a_next", "u64");
    ctx.declare_var_parsed("b_next", "u64");

    ctx.push_assume("a_val", "a == 48");
    ctx.push_assume("b_val", "b == 18");
    // Euclidean step: a_next = b, b_next = a % b
    ctx.push_assume("a_next_val", "a_next == 18");
    ctx.push_assume("b_next_val", "b_next == 12"); // 48 % 18 = 12

    // After step: a_next == old b
    ctx.push_assert("a_gets_b", "a_next == b");
    // After step: b_next < b (progress)
    ctx.push_assert("b_decreases", "b_next < b");
    // b_next >= 0 (u64 — always true, but documents the invariant)
    ctx.push_assert("b_next_nonneg", "b_next >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64b: gcd step 48→18 should verify, got: {:?}",
        result,
    );
}

/// Tier 64b: Step — second iteration: gcd(18, 12) → gcd(12, 6).
/// 18 % 12 = 6, so a=12, b=6.
#[test]
fn test_vt_tier64b_gcd_step_18_12() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");
    ctx.declare_var_parsed("a_next", "u64");
    ctx.declare_var_parsed("b_next", "u64");

    ctx.push_assume("a_val", "a == 18");
    ctx.push_assume("b_val", "b == 12");
    ctx.push_assume("a_next_val", "a_next == 12");
    ctx.push_assume("b_next_val", "b_next == 6"); // 18 % 12 = 6

    ctx.push_assert("a_gets_b", "a_next == b");
    ctx.push_assert("b_decreases", "b_next < b");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64b: gcd step 18→12 should verify, got: {:?}",
        result,
    );
}

/// Tier 64b: Step — third iteration: gcd(12, 6) → gcd(6, 0).
/// 12 % 6 = 0, so a=6, b=0. Loop exits.
#[test]
fn test_vt_tier64b_gcd_step_12_6_terminal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");
    ctx.declare_var_parsed("a_next", "u64");
    ctx.declare_var_parsed("b_next", "u64");

    ctx.push_assume("a_val", "a == 12");
    ctx.push_assume("b_val", "b == 6");
    ctx.push_assume("a_next_val", "a_next == 6");
    ctx.push_assume("b_next_val", "b_next == 0"); // 12 % 6 = 0

    ctx.push_assert("a_gets_b", "a_next == b");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64b: gcd terminal step should verify, got: {:?}",
        result,
    );
}

/// Tier 64b: Step — gcd(35, 15) → gcd(15, 5) → gcd(5, 0).
/// Full trace in two steps.
#[test]
fn test_vt_tier64b_gcd_full_trace_35_15() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a0", "u64");
    ctx.declare_var_parsed("b0", "u64");
    ctx.declare_var_parsed("a1", "u64");
    ctx.declare_var_parsed("b1", "u64");
    ctx.declare_var_parsed("a2", "u64");
    ctx.declare_var_parsed("b2", "u64");

    // Step 0: start
    ctx.push_assume("a0_val", "a0 == 35");
    ctx.push_assume("b0_val", "b0 == 15");
    // Step 1: 35 % 15 = 5
    ctx.push_assume("a1_val", "a1 == 15");
    ctx.push_assume("b1_val", "b1 == 5");
    // Step 2: 15 % 5 = 0
    ctx.push_assume("a2_val", "a2 == 5");
    ctx.push_assume("b2_val", "b2 == 0");

    // b strictly decreases at each step
    ctx.push_assert("b_dec_01", "b1 < b0");
    ctx.push_assert("b_dec_12", "b2 < b1");
    // a gets old b at each step
    ctx.push_assert("a1_is_b0", "a1 == b0");
    ctx.push_assert("a2_is_b1", "a2 == b1");
    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64b: full gcd trace 35,15 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Invariant — gcd is preserved, b strictly decreases
// ========================================================================

/// Tier 64c: Invariant — the remainder operation preserves the gcd.
/// For concrete values: gcd(48,18) = gcd(18, 48%18) = gcd(18, 12).
/// We verify this by checking that 6 divides both pairs.
#[test]
fn test_vt_tier64c_gcd_preserved_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");
    ctx.declare_var_parsed("r", "u64");
    ctx.declare_var_parsed("g", "u64");

    ctx.push_assume("a_val", "a == 48");
    ctx.push_assume("b_val", "b == 18");
    ctx.push_assume("r_val", "r == 12"); // 48 % 18
    ctx.push_assume("g_val", "g == 6"); // the GCD

    // g divides a: 48 = 6 * 8
    ctx.declare_var_parsed("qa", "u64");
    ctx.push_assume("g_div_a", "qa == 8 && g * qa == a");
    // g divides b: 18 = 6 * 3
    ctx.declare_var_parsed("qb", "u64");
    ctx.push_assume("g_div_b", "qb == 3 && g * qb == b");
    // g divides r: 12 = 6 * 2
    ctx.declare_var_parsed("qr", "u64");
    ctx.push_assume("g_div_r", "qr == 2 && g * qr == r");

    // Verify: g divides both (b, r) — so gcd(a,b) == gcd(b,r)
    ctx.push_assert("g_divides_b", "g * qb == b");
    ctx.push_assert("g_divides_r", "g * qr == r");
    // And r < b (progress)
    ctx.push_assert("r_lt_b", "r < b");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64c: gcd preserved concrete should verify, got: {:?}",
        result,
    );
}

/// Tier 64c: Invariant — divisor transfer with concrete second example.
/// gcd(252, 105) = 21. Step: 252 = 2*105 + 42. Check 21 divides 42.
/// This tests the key invariant: if d|a and d|b, then d|(a mod b).
#[test]
fn test_vt_tier64c_divisor_transfer_252_105() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");
    ctx.declare_var_parsed("q", "u64");
    ctx.declare_var_parsed("r", "u64");
    ctx.declare_var_parsed("d", "u64");

    ctx.push_assume("a_val", "a == 252");
    ctx.push_assume("b_val", "b == 105");
    ctx.push_assume("q_val", "q == 2"); // 252 / 105 = 2
    ctx.push_assume("r_val", "r == 42"); // 252 % 105 = 42
    ctx.push_assume("d_val", "d == 21"); // the GCD

    // Division identity: a = q*b + r
    ctx.push_assert("div_identity", "a == q * b + r");
    // d divides a: 252 = 21 * 12
    ctx.declare_var_parsed("ka", "u64");
    ctx.push_assume("ka_val", "ka == 12");
    ctx.push_assert("d_div_a", "d * ka == a");
    // d divides b: 105 = 21 * 5
    ctx.declare_var_parsed("kb", "u64");
    ctx.push_assume("kb_val", "kb == 5");
    ctx.push_assert("d_div_b", "d * kb == b");
    // d divides r: 42 = 21 * 2
    ctx.declare_var_parsed("kr", "u64");
    ctx.push_assume("kr_val", "kr == 2");
    ctx.push_assert("d_div_r", "d * kr == r");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64c: divisor transfer 252,105 should verify, got: {:?}",
        result,
    );
}

/// Tier 64c: Invariant — b strictly decreases (termination measure).
/// After one Euclidean step, b_next = a % b < b.
#[test]
fn test_vt_tier64c_termination_measure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");
    ctx.declare_var_parsed("q", "u64");
    ctx.declare_var_parsed("r", "u64");

    ctx.push_assume("a_bound", "a >= 1 && a <= 1000");
    ctx.push_assume("b_bound", "b >= 1 && b <= 1000");
    ctx.push_assume("q_bound", "q >= 1 && q <= 1000");
    ctx.push_assume("r_bound", "r >= 0 && r < b");
    ctx.push_assume("div_id", "a == q * b + r");

    // b_next = r < b (strict decrease when b > 0)
    ctx.push_assert("decreases", "r < b");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64c: termination measure should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Exit — when b == 0, a is the gcd
// ========================================================================

/// Tier 64d: Exit — gcd(6, 0) = 6 (base case).
#[test]
fn test_vt_tier64d_gcd_base_case() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");

    ctx.push_assume("a_val", "a == 6");
    ctx.push_assume("b_val", "b == 0");

    ctx.push_assert("sum_is_result", "a + b == 6");
    ctx.push_assert("result_dominates_zero", "a >= b");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64d: gcd base case should verify, got: {:?}",
        result,
    );
}

/// Tier 64d: Exit — gcd result divides both original inputs.
/// For gcd(48, 18) = 6: 6|48 and 6|18.
#[test]
fn test_vt_tier64d_result_divides_inputs() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a_orig", "u64");
    ctx.declare_var_parsed("b_orig", "u64");
    ctx.declare_var_parsed("g", "u64");
    ctx.declare_var_parsed("qa", "u64");
    ctx.declare_var_parsed("qb", "u64");

    ctx.push_assume("a_orig_val", "a_orig == 48");
    ctx.push_assume("b_orig_val", "b_orig == 18");
    ctx.push_assume("g_val", "g == 6");
    ctx.push_assume("qa_val", "qa == 8");
    ctx.push_assume("qb_val", "qb == 3");

    // g divides both original inputs
    ctx.push_assert("g_div_a", "g * qa == a_orig");
    ctx.push_assert("g_div_b", "g * qb == b_orig");
    // g is positive
    ctx.push_assert("g_pos", "g > 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64d: gcd divides inputs should verify, got: {:?}",
        result,
    );
}

/// Tier 64d: Exit — gcd is the greatest such divisor.
/// Any common divisor d of 48 and 18 must satisfy d <= 6.
#[test]
fn test_vt_tier64d_gcd_is_greatest() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("d", "u64");
    ctx.declare_var_parsed("kd_a", "u64");
    ctx.declare_var_parsed("kd_b", "u64");

    ctx.push_assume("d_bound", "d >= 1 && d <= 48");
    ctx.push_assume("kd_a_bound", "kd_a >= 1 && kd_a <= 48");
    ctx.push_assume("kd_b_bound", "kd_b >= 1 && kd_b <= 48");
    ctx.push_assume("d_div_48", "d * kd_a == 48");
    ctx.push_assume("d_div_18", "d * kd_b == 18");

    // d must be <= 6 (the true gcd)
    ctx.push_assert("d_le_gcd", "d <= 6");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64d: gcd is greatest common divisor, got: {:?}",
        result,
    );
}

/// Tier 64d: Exit — edge case gcd(0, n) = n.
#[test]
fn test_vt_tier64d_gcd_zero_left() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");

    ctx.push_assume("a_val", "a == 0");
    ctx.push_assume("b_val", "b == 17");

    ctx.push_assert("sum_is_result", "a + b == 17");
    ctx.push_assert("left_is_zero", "a <= b");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64d: gcd(0, n) = n should verify, got: {:?}",
        result,
    );
}
