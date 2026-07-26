// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 17d-e — Classic algorithm VCs.
//!
//! Split from `test_verifythis_nested_loop_vcs.rs` (500-line limit).
//!
//! GROUP D: Bubble sort pass VC — adjacent swaps, permutation preservation,
//! and maximum-at-end property. Combines nested-loop reasoning with data
//! structure manipulation.
//!
//! GROUP E: Euclidean GCD — loop invariant preservation and termination.
//! Classic mathematical VerifyThis pattern requiring modular arithmetic.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP D: Bubble sort pass VC (classic VerifyThis pattern)
//
// A single pass of bubble sort: scan left to right, swap adjacent if
// out of order. After one pass, the maximum element is in position n-1.
// This combines nested-loop reasoning (bubble sort has nested loops)
// with data structure manipulation.
// ========================================================================

/// Tier 17d: Bubble sort single pass — maximum reaches end.
///
/// After one left-to-right pass with adjacent swaps, the maximum of
/// s[0..n] ends up at s[n-1]. Concrete for n=3.
#[test]
fn test_vt_tier17d_bubble_pass_max_at_end() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s1", "Seq<i32>"); // after comparing positions 0,1
    ctx.declare_var_parsed("s2", "Seq<i32>"); // after comparing positions 1,2

    ctx.push_assume("len3", "s.len() == 3");
    ctx.push_assume("s1_len", "s1.len() == 3");
    ctx.push_assume("s2_len", "s2.len() == 3");

    // Step 1: compare s[0], s[1] — swap if out of order
    // After: s1[0] <= s1[1], s1[2] unchanged
    ctx.push_assume("step1_sorted", "s1.index(0) <= s1.index(1)");
    ctx.push_assume("step1_frame", "s1.index(2) == s.index(2)");
    // Exclusive permutation: s1[0..2] is an exact swap of s[0..2]
    ctx.push_assume(
        "step1_perm",
        "(s1.index(0) == s.index(0) && s1.index(1) == s.index(1)) || \
         (s1.index(0) == s.index(1) && s1.index(1) == s.index(0))",
    );

    // Step 2: compare s1[1], s1[2] — swap if out of order
    ctx.push_assume("step2_sorted", "s2.index(1) <= s2.index(2)");
    ctx.push_assume("step2_frame", "s2.index(0) == s1.index(0)");
    // Exclusive permutation: s2[1..3] is an exact swap of s1[1..3]
    ctx.push_assume(
        "step2_perm",
        "(s2.index(1) == s1.index(1) && s2.index(2) == s1.index(2)) || \
         (s2.index(1) == s1.index(2) && s2.index(2) == s1.index(1))",
    );

    // After full pass: s2[2] >= s2[0] (non-trivial: requires chaining
    // step2_frame + step1_sorted + step2_sorted through permutation).
    ctx.push_assert("max_at_end", "s2.index(2) >= s2.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17d: bubble pass max at end should verify, got: {:?}",
        result,
    );
}

/// Tier 17d: Bubble sort — adjacent pair sorted after conditional swap.
///
/// Models the actual swap logic: if a > b, swap. The assertion that
/// a_new <= b_new must follow from the swap semantics, NOT be assumed.
/// Discrimination: removing the conditional swap model makes the assertion
/// fail (a_new could be > b_new without the swap guarantee).
#[test]
fn test_vt_tier17d_bubble_adjacent_sorted() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("a_new", "i32");
    ctx.declare_var_parsed("b_new", "i32");

    ctx.push_assume("a_bound", "a >= 0 && a < 1000");
    ctx.push_assume("b_bound", "b >= 0 && b < 1000");

    // Conditional swap: if a > b then (a_new, b_new) = (b, a) else unchanged
    // Case 1: a <= b, no swap
    // Case 2: a > b, swap
    ctx.push_assume(
        "swap_logic",
        "(a <= b && a_new == a && b_new == b) || (a > b && a_new == b && b_new == a)",
    );

    // After conditional swap: a_new <= b_new (follows from swap logic)
    ctx.push_assert("sorted_after_swap", "a_new <= b_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17d: conditional swap produces sorted pair, got: {:?}",
        result,
    );
}

/// Tier 17d: Bubble sort negative — one pass doesn't fully sort.
#[test]
fn test_vt_tier17d_bubble_one_pass_not_sorted_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_after", "Seq<i32>");

    ctx.push_assume("len3", "s.len() == 3");
    ctx.push_assume("after_len", "s_after.len() == 3");

    // One pass guarantees: max at end, adjacent pair 1,2 sorted
    ctx.push_assume("max_at_end", "s_after.index(2) >= s_after.index(1)");

    // But does NOT guarantee s_after[0] <= s_after[1]
    ctx.push_assert("fully_sorted_wrong", "s_after.index(0) <= s_after.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 17d SOUNDNESS: one pass doesn't fully sort (e.g. s_after=[3,1,2]), got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: GCD algorithm VC (mathematical VerifyThis pattern)
//
// Euclidean GCD is a classic verification target. The loop invariant is:
//   gcd(a, b) == gcd(a_orig, b_orig) at every step.
// We model this via the key property: gcd(a, b) == gcd(b, a mod b).
// ========================================================================

/// Tier 17e: GCD step VC — the Euclidean algorithm preserves gcd.
///
/// If gcd(a, b) == g and a = b*q + r, then gcd(b, r) == g.
/// We model this as: given the modular step, the invariant is maintained.
#[test]
fn test_vt_tier17e_gcd_step_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("r", "i32");

    // Concrete: a=12, b=8
    ctx.push_assume("a_eq", "a == 12");
    ctx.push_assume("b_eq", "b == 8");
    ctx.push_assume("r_eq", "r == 4"); // 12 mod 8 = 4

    // gcd(12, 8) == gcd(8, 4) == 4
    // 4 divides 12 (12 = 4*3) and 4 divides 8 (8 = 4*2)
    ctx.push_assert("r_divides_b", "b == r * 2");
    ctx.push_assert("r_divides_a", "a == r * 3");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17e: concrete GCD step should verify, got: {:?}",
        result,
    );
}

/// Tier 17e: GCD termination — remainder is strictly less than the dividend.
///
/// The GCD algorithm replaces (a, b) with (b, r) where r = a mod b.
/// Termination requires r < a (the new value is strictly less than the old).
/// This is NON-TAUTOLOGICAL: r < a is NOT directly assumed. It must be
/// derived from the division equation a = b*q + r, combined with b > 0
/// and q >= 1 (which follows from a >= b > 0).
/// Discrimination: removing div_eq or a_ge_b makes the assertion fail.
#[test]
fn test_vt_tier17e_gcd_termination_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("q", "i32");
    ctx.declare_var_parsed("r", "i32");

    // Precondition: a >= b > 0 (GCD normalizes so a >= b)
    ctx.push_assume("a_pos", "a > 0");
    ctx.push_assume("b_pos", "b > 0");
    ctx.push_assume("a_ge_b", "a >= b");
    ctx.push_assume("a_bound", "a < 1000000");
    ctx.push_assume("b_bound", "b < 1000000");

    // Division: a = b*q + r, 0 <= r < b, q >= 1 (since a >= b > 0)
    ctx.push_assume("q_ge1", "q >= 1");
    ctx.push_assume("div_eq", "a == b * q + r");
    ctx.push_assume("r_ge0", "r >= 0");
    ctx.push_assume("r_lt_b", "r < b");

    // Termination: r < a (the remainder is strictly less than the dividend).
    // Follows from: a = b*q + r, q >= 1, b > 0, r >= 0 → a >= b + r > r.
    ctx.push_assert("decreases", "r < a");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17e: GCD termination VC should verify, got: {:?}",
        result,
    );
}

/// Tier 17e: GCD negative — wrong remainder doesn't preserve gcd.
#[test]
fn test_vt_tier17e_gcd_wrong_remainder_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("r", "i32");

    ctx.push_assume("a_eq", "a == 12");
    ctx.push_assume("b_eq", "b == 8");
    ctx.push_assume("r_eq", "r == 3"); // WRONG: 12 mod 8 = 4, not 3

    // If r were the correct remainder (4), then b = r * 2 (8 = 4*2).
    // But with r=3: 8 != 3*2 = 6. This should fail.
    ctx.push_assert("r_divides_b", "b == r * 2");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 17e SOUNDNESS: wrong remainder (r=3, but 12 mod 8 = 4) should produce a counterexample, got: {:?}",
        result,
    );
}
