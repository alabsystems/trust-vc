// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 64 — GCD Euclidean VCs (Groups E–F).
//!
//! Extended traces and soundness negatives for the Euclidean GCD algorithm.
//! Core groups (A–D) are in test_verifythis_gcd_euclidean.rs.
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
// GROUP E: Extended — larger values and coprime pairs
// ========================================================================

/// Tier 64e: Extended — gcd of coprime pair (17, 13) = 1.
/// Trace: 17,13 → 13,4 → 4,1 → 1,0 → result 1.
#[test]
fn test_vt_tier64e_coprime_17_13() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a0", "u64");
    ctx.declare_var_parsed("b0", "u64");
    ctx.declare_var_parsed("a1", "u64");
    ctx.declare_var_parsed("b1", "u64");
    ctx.declare_var_parsed("a2", "u64");
    ctx.declare_var_parsed("b2", "u64");
    ctx.declare_var_parsed("a3", "u64");
    ctx.declare_var_parsed("b3", "u64");

    ctx.push_assume("s0a", "a0 == 17");
    ctx.push_assume("s0b", "b0 == 13");
    ctx.push_assume("s1a", "a1 == 13");
    ctx.push_assume("s1b", "b1 == 4"); // 17 % 13 = 4
    ctx.push_assume("s2a", "a2 == 4");
    ctx.push_assume("s2b", "b2 == 1"); // 13 % 4 = 1
    ctx.push_assume("s3a", "a3 == 1");
    ctx.push_assume("s3b", "b3 == 0"); // 4 % 1 = 0

    // Monotone b decrease
    ctx.push_assert("dec_01", "b1 < b0");
    ctx.push_assert("dec_12", "b2 < b1");
    ctx.push_assert("dec_23", "b3 < b2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64e: coprime gcd(17,13)=1 should verify, got: {:?}",
        result,
    );
}

/// Tier 64e: Extended — gcd(252, 105) = 21.
/// Trace: 252,105 → 105,42 → 42,21 → 21,0.
#[test]
fn test_vt_tier64e_gcd_252_105() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a0", "u64");
    ctx.declare_var_parsed("b0", "u64");
    ctx.declare_var_parsed("a1", "u64");
    ctx.declare_var_parsed("b1", "u64");
    ctx.declare_var_parsed("a2", "u64");
    ctx.declare_var_parsed("b2", "u64");
    ctx.declare_var_parsed("a3", "u64");
    ctx.declare_var_parsed("b3", "u64");

    ctx.push_assume("s0a", "a0 == 252");
    ctx.push_assume("s0b", "b0 == 105");
    ctx.push_assume("s1a", "a1 == 105");
    ctx.push_assume("s1b", "b1 == 42"); // 252 % 105 = 42
    ctx.push_assume("s2a", "a2 == 42");
    ctx.push_assume("s2b", "b2 == 21"); // 105 % 42 = 21
    ctx.push_assume("s3a", "a3 == 21");
    ctx.push_assume("s3b", "b3 == 0"); // 42 % 21 = 0

    ctx.push_assert("dec_01", "b1 < b0");
    ctx.push_assert("dec_12", "b2 < b1");
    ctx.push_assert("dec_23", "b3 < b2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64e: gcd(252,105)=21 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Soundness negatives
// ========================================================================

/// Tier 64f NEGATIVE: wrong remainder breaks the invariant.
/// If we claim 48 % 18 = 10 (wrong — it's 12), the step fails.
#[test]
fn test_vt_tier64f_wrong_remainder_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");
    ctx.declare_var_parsed("r", "u64");

    ctx.push_assume("a_val", "a == 48");
    ctx.push_assume("b_val", "b == 18");
    ctx.push_assume("r_wrong", "r == 10"); // WRONG: 48 % 18 = 12, not 10

    // If r is the correct remainder, then a == (a/b)*b + r
    // 48 == 2*18 + r → r should be 12
    // With r=10: 2*18 + 10 = 46 ≠ 48
    ctx.declare_var_parsed("q", "u64");
    ctx.push_assume("q_val", "q == 2");
    ctx.push_assert("div_identity", "q * b + r == a");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 64f SOUNDNESS: wrong remainder must be rejected, got: {:?}",
        result,
    );
}

/// Tier 64f NEGATIVE: claiming gcd(48, 18) = 9 is wrong.
/// 9 does not divide 48 (48/9 = 5.33...).
#[test]
fn test_vt_tier64f_wrong_gcd_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("g", "u64");
    ctx.declare_var_parsed("qa", "u64");
    ctx.declare_var_parsed("qb", "u64");

    ctx.push_assume("g_val", "g == 9");
    ctx.push_assume("qa_bound", "qa >= 1 && qa <= 48");
    ctx.push_assume("qb_bound", "qb >= 1 && qb <= 48");

    // Claim: g divides both 48 and 18
    // 9 * qa == 48 has no integer solution (48/9 is not an integer)
    ctx.push_assert("g_div_48", "g * qa == 48");
    ctx.push_assert("g_div_18", "g * qb == 18");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 64f SOUNDNESS: wrong gcd=9 must be rejected, got: {:?}",
        result,
    );
}

/// Tier 64f NEGATIVE: swapping operands in the step gives wrong result.
/// Euclidean step is (b, a%b), NOT (a%b, b). If we swap, b doesn't decrease.
#[test]
fn test_vt_tier64f_swapped_operands_no_progress() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");
    ctx.declare_var_parsed("a_next", "u64");
    ctx.declare_var_parsed("b_next", "u64");

    ctx.push_assume("a_val", "a == 48");
    ctx.push_assume("b_val", "b == 18");
    // WRONG step: a_next = a%b, b_next = b (should be a_next=b, b_next=a%b)
    ctx.push_assume("a_next_wrong", "a_next == 12"); // 48 % 18
    ctx.push_assume("b_next_wrong", "b_next == 18"); // b unchanged!

    // b should strictly decrease — but it doesn't with the wrong step
    ctx.push_assert("b_decreases", "b_next < b");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 64f SOUNDNESS: swapped operands must fail progress, got: {:?}",
        result,
    );
}

/// Tier 64f NEGATIVE: claiming gcd(17, 13) = 2 is wrong (they're coprime).
#[test]
fn test_vt_tier64f_coprime_wrong_gcd_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("g", "u64");
    ctx.declare_var_parsed("qa", "u64");
    ctx.declare_var_parsed("qb", "u64");

    ctx.push_assume("g_val", "g == 2");
    ctx.push_assume("qa_bound", "qa >= 1 && qa <= 17");
    ctx.push_assume("qb_bound", "qb >= 1 && qb <= 17");

    // 2 does not divide 17 (17/2 = 8.5) or 13 (13/2 = 6.5)
    ctx.push_assert("g_div_17", "g * qa == 17");
    ctx.push_assert("g_div_13", "g * qb == 13");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 64f SOUNDNESS: wrong gcd of coprimes must be rejected, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP G: Symbolic Divisor Preservation (VerifyThis 2015 C2 pattern)
//
// The core VerifyThis GCD property: if d divides x and d divides y,
// then d divides (x mod y). This requires arithmetic normalization
// (distribution, back-propagation, additive cancellation) to discharge
// symbolically. Mirrors the repaired gcd_2015_c2 practice benchmark
// from win-all-software-proof-competitions.
//
// Part of #2187 (VerifyThis competition readiness).
// ========================================================================

/// Tier 64g: Symbolic divisor preservation — full GCD lemma chain.
///
/// Given: d | x (x == d*q1), d | y (y == d*q2), x == q*y + r,
///        q1 == q*q2 + q3 (witness relation).
/// Prove: r == d*q3 (d divides the remainder).
///
/// This is the key VerifyThis 2015 Challenge 2 property. It requires
/// arithmetic normalization: substitution of y→d*q2 into x==q*y+r,
/// back-propagation of q1→q*q2+q3 into x==d*q1, distribution of
/// d*(q*q2+q3)→d*q*q2+d*q3, and additive cancellation.
#[test]
fn test_vt_tier64g_symbolic_divisor_preservation() {
    let mut ctx = VerificationContext::new();
    // All int-mode (not u32/u64) — avoids overflow concerns
    ctx.declare_var_parsed("d", "int");
    ctx.declare_var_parsed("q", "int");
    ctx.declare_var_parsed("q1", "int");
    ctx.declare_var_parsed("q2", "int");
    ctx.declare_var_parsed("q3", "int");
    ctx.declare_var_parsed("r", "int");
    ctx.declare_var_parsed("x", "int");
    ctx.declare_var_parsed("y", "int");

    // d divides y
    ctx.push_assume("y_def", "y == d * q2");
    // division identity
    ctx.push_assume("x_div", "x == q * y + r");
    // witness relation
    ctx.push_assume("q1_def", "q1 == q * q2 + q3");
    // d divides x
    ctx.push_assume("x_d", "x == d * q1");

    // The key assertion: d divides the remainder
    ctx.push_assert("d_divides_r", "r == d * q3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64g: symbolic divisor preservation (gcd_2015_c2 pattern) \
         should verify via arithmetic normalization, got: {:?}",
        result,
    );
}

/// Tier 64g: Intermediate step — q*y == d*(q*q2) via substitution.
///
/// Given y == d*q2, prove q*y == d*(q*q2). This is the first step
/// in the divisor preservation chain.
#[test]
fn test_vt_tier64g_step1_q_mul_y() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("d", "int");
    ctx.declare_var_parsed("q", "int");
    ctx.declare_var_parsed("q2", "int");
    ctx.declare_var_parsed("y", "int");

    ctx.push_assume("y_def", "y == d * q2");
    ctx.push_assert("step1", "q * y == d * (q * q2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64g STEP 1: q*y == d*(q*q2) should verify, got: {:?}",
        result,
    );
}

/// Tier 64g: Intermediate step — x == d*(q*q2) + r via chained substitution.
///
/// Given y == d*q2 and x == q*y + r, prove x == d*(q*q2) + r.
#[test]
fn test_vt_tier64g_step2_x_expanded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("d", "int");
    ctx.declare_var_parsed("q", "int");
    ctx.declare_var_parsed("q2", "int");
    ctx.declare_var_parsed("r", "int");
    ctx.declare_var_parsed("x", "int");
    ctx.declare_var_parsed("y", "int");

    ctx.push_assume("y_def", "y == d * q2");
    ctx.push_assume("x_def", "x == q * y + r");
    ctx.push_assert("step2", "x == d * (q * q2) + r");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64g STEP 2: x == d*(q*q2) + r should verify, got: {:?}",
        result,
    );
}

/// Tier 64g: Intermediate step — x == d*(q*q2 + q3) via back-propagation.
///
/// Given x == d*q1 and q1 == q*q2 + q3, prove x == d*(q*q2 + q3).
#[test]
fn test_vt_tier64g_step3_back_propagation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("d", "int");
    ctx.declare_var_parsed("q", "int");
    ctx.declare_var_parsed("q1", "int");
    ctx.declare_var_parsed("q2", "int");
    ctx.declare_var_parsed("q3", "int");
    ctx.declare_var_parsed("x", "int");

    ctx.push_assume("x_def", "x == d * q1");
    ctx.push_assume("q1_def", "q1 == q * q2 + q3");
    ctx.push_assert("step3", "x == d * (q * q2 + q3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 64g STEP 3: x == d*(q*q2+q3) via back-propagation, got: {:?}",
        result,
    );
}

/// Tier 64g NEGATIVE: without the witness relation, divisor preservation
/// is false — there exists a counterexample where d|x and d|y but
/// d does not divide r for the given q3.
#[test]
fn test_vt_tier64g_no_witness_fails() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("d", "int");
    ctx.declare_var_parsed("q", "int");
    ctx.declare_var_parsed("q1", "int");
    ctx.declare_var_parsed("q2", "int");
    ctx.declare_var_parsed("q3", "int");
    ctx.declare_var_parsed("r", "int");
    ctx.declare_var_parsed("x", "int");
    ctx.declare_var_parsed("y", "int");

    ctx.push_assume("y_def", "y == d * q2");
    ctx.push_assume("x_div", "x == q * y + r");
    // MISSING: q1 == q * q2 + q3 (the witness relation)
    ctx.push_assume("x_d", "x == d * q1");

    // Without the witness, q3 is unconstrained — r == d*q3 is false
    ctx.push_assert("d_divides_r", "r == d * q3");

    let result = verify_with_pipeline(ctx);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "TIER 64g NEGATIVE: without witness relation, divisor preservation \
         should NOT verify, got: {:?}",
        result,
    );
}
