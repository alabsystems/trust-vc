// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 14 — Data structure manipulation VCs.
//!
//! Tiers 1-13 test quantifiers, sortedness, and single-sequence reasoning.
//! Tier 14 tests **data structure manipulation patterns** from real VerifyThis
//! problems: swap, frame conditions, conditional updates, and partitioning.
//!
//! These patterns appear in nearly every VerifyThis sorting/array problem
//! (mergesort with runs 2022, persistent arrays 2025, etc.).
//!
//! KEY LESSON: Frame conditions (proving what DOESN'T change) are as important
//! as proving what does change. Most VerifyThis solutions need both.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Swap operations
//
// Swap is the most common primitive in sorting/array VerifyThis problems.
// A swap at positions i, j in sequence s produces s_new where:
//   s_new[i] == s[j], s_new[j] == s[i], and all other elements unchanged.
// ========================================================================

/// Tier 14a: Swap postcondition — elements at i,j are exchanged.
#[test]
fn test_vt_tier14a_swap_postcondition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("i_valid", "i < n");
    ctx.push_assume("j_valid", "j < n");
    ctx.push_assume("i_ne_j", "i != j");
    // Swap semantics
    ctx.push_assume("swap_i", "s_new.index(i) == s.index(j)");
    ctx.push_assume("swap_j", "s_new.index(j) == s.index(i)");

    ctx.push_assert(
        "swap_pair",
        "s_new.index(i) == s.index(j) && s_new.index(j) == s.index(i)",
    );
    ctx.push_assert("len_preserved", "s_new.len() == s.len()");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14a: swap postcondition should verify, got: {:?}",
        result,
    );
}

/// Tier 14a: Swap frame condition — all other elements unchanged.
/// This is the critical frame property: only positions i and j change.
#[test]
fn test_vt_tier14a_swap_frame_condition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("i_valid", "i < n");
    ctx.push_assume("j_valid", "j < n");
    ctx.push_assume("i_ne_j", "i != j");
    // Swap semantics
    ctx.push_assume("swap_i", "s_new.index(i) == s.index(j)");
    ctx.push_assume("swap_j", "s_new.index(j) == s.index(i)");
    // Frame: all other positions unchanged
    ctx.push_assume(
        "frame",
        "forall(|k: u64| !(k < n && k != i && k != j) || s_new.index(k) == s.index(k))",
    );

    // Verify: a specific non-swapped position is unchanged
    // Pick k=0 when neither i nor j is 0
    ctx.push_assume("i_ne_0", "i != 0");
    ctx.push_assume("j_ne_0", "j != 0");
    ctx.push_assert("frame_at_0", "s_new.index(0) == s.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14a: swap frame at index 0 should verify, got: {:?}",
        result,
    );
}

/// Tier 14a: Swap soundness negative — frame does not hold at swapped position.
#[test]
fn test_vt_tier14a_swap_frame_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("i_valid", "i < n");
    ctx.push_assume("j_valid", "j < n");
    ctx.push_assume("i_ne_j", "i != j");
    ctx.push_assume("swap_i", "s_new.index(i) == s.index(j)");
    ctx.push_assume("swap_j", "s_new.index(j) == s.index(i)");

    // WRONG: claiming s_new[i] == s[i] (only true when s[i] == s[j])
    ctx.push_assert("wrong_frame_at_i", "s_new.index(i) == s.index(i)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 14a SOUNDNESS: swap frame negative (e.g. s=[1,2], i=0, j=1) should produce a counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Conditional update VCs (if-else in loop body)
//
// Most loop bodies have if-else branches. The verification must show
// the invariant is preserved regardless of which branch executes.
// ========================================================================

/// Tier 14b: Conditional max update — "if s[i] > max then max = s[i]"
/// Both branches must preserve the invariant.
#[test]
fn test_vt_tier14b_conditional_max_update_taken() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("max_new", "i32");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("i_valid", "i < n");
    // Branch TAKEN: s[i] > max, so max_new = s[i]
    ctx.push_assume("branch_taken", "s.index(i) > max_val");
    ctx.push_assume("update", "max_new == s.index(i)");

    // Must show: max_new >= s[i]
    ctx.push_assert("new_covers_i", "max_new >= s.index(i)");
    // Must show: max_new >= max_val (monotonicity)
    ctx.push_assert("new_ge_old", "max_new >= max_val");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14b: taken branch of conditional max should verify, got: {:?}",
        result,
    );
}

/// Tier 14b: Conditional max update — branch NOT taken (s[i] <= max).
#[test]
fn test_vt_tier14b_conditional_max_update_not_taken() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("max_new", "i32");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("i_valid", "i < n");
    // Branch NOT taken: s[i] <= max, max unchanged
    ctx.push_assume("branch_not_taken", "s.index(i) <= max_val");
    ctx.push_assume("no_update", "max_new == max_val");

    // Must show: max_new >= s[i] (from branch condition)
    ctx.push_assert("new_covers_i", "max_new >= s.index(i)");
    // Must show: max_new >= max_val (identity)
    ctx.push_assert("new_ge_old", "max_new >= max_val");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14b: not-taken branch of conditional max should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Partition VCs (Dutch National Flag / quicksort partition)
//
// Partition is the core operation in quicksort and Dutch National Flag,
// both classic VerifyThis problems. The invariant tracks three regions:
//   [0, lo)    — elements < pivot
//   [lo, hi)   — unprocessed (or equal to pivot)
//   [hi, n)    — elements > pivot
// ========================================================================

/// Tier 14c: Partition init VC — trivially, empty regions satisfy the invariant.
#[test]
fn test_vt_tier14c_partition_init_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("pivot", "i32");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");
    // Initial state: lo = 0, hi = n (no elements classified)
    ctx.push_assume("lo_init", "lo == 0");
    ctx.push_assume("hi_init", "hi == n");

    // Invariant: all elements in [0, lo) are < pivot
    // Vacuously true when lo == 0
    ctx.push_assert(
        "low_region_vacuous",
        "forall(|k: u64| !(k < lo) || s.index(k) < pivot)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14c: partition init VC (vacuous) should verify, got: {:?}",
        result,
    );
}

/// Tier 14c: Partition step VC — classifying s[lo] < pivot extends low region.
/// BV overflow guard: lo < 1000000 prevents lo+1 wraparound.
#[test]
fn test_vt_tier14c_partition_step_classify_low() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("pivot", "i32");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("lo_new", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("lo_bounded", "lo < 1000000");
    ctx.push_assume("lo_lt_n", "lo < n");
    // Invariant IH: all elements in [0, lo) are < pivot
    ctx.push_assume("inv_ih", "forall(|k: u64| !(k < lo) || s.index(k) < pivot)");
    // Current element is < pivot
    ctx.push_assume("elem_lt_pivot", "s.index(lo) < pivot");
    // Advance lo
    ctx.push_assume("lo_step", "lo_new == lo + 1");

    // Invariant preserved: all elements in [0, lo_new) are < pivot
    ctx.push_assert(
        "inv_preserved",
        "forall(|k: u64| !(k < lo_new) || s.index(k) < pivot)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14c: partition step (classify low) should verify, got: {:?}",
        result,
    );
}

/// Tier 14c: Partition soundness negative — wrong classification.
#[test]
fn test_vt_tier14c_partition_negative_wrong_region() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("pivot", "i32");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge3", "n >= 3");
    ctx.push_assume("lo_ge1", "lo >= 1");
    ctx.push_assume("lo_lt_n", "lo < n");
    // Only know elements in [0, lo) are < pivot
    ctx.push_assume("inv", "forall(|k: u64| !(k < lo) || s.index(k) < pivot)");
    // Concrete witness keeps this negative in the reliable Counterexample
    // bucket: the classified prefix satisfies the invariant, while s[lo] is
    // unprocessed and can equal the pivot.
    ctx.push_assume("n_witness", "n == 3");
    ctx.push_assume("lo_witness", "lo == 1");
    ctx.push_assume("pivot_witness", "pivot == 0");
    ctx.push_assume("classified_prefix_witness", "s.index(0) == -1");
    ctx.push_assume("unprocessed_witness", "s.index(lo) == pivot");

    // WRONG: claiming s[lo] < pivot (lo is unprocessed, not classified)
    ctx.push_assert("wrong_claim", "s.index(lo) < pivot");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 14c SOUNDNESS: an unprocessed partition element (e.g. s[lo] >= pivot) should produce a counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Two-accumulator loop (summing two quantities)
//
// Many VerifyThis problems track multiple quantities in a single loop.
// The invariant must relate all accumulators to each other and to the
// loop counter.
// ========================================================================

/// Tier 14d: Two accumulators — even_count + odd_count == i at each step.
/// BV overflow guard: i < 1000000.
#[test]
fn test_vt_tier14d_two_accumulators_sum_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("even_count", "u64");
    ctx.declare_var_parsed("odd_count", "u64");
    ctx.declare_var_parsed("even_new", "u64");
    ctx.declare_var_parsed("odd_new", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("elem_is_even", "u64");

    ctx.push_assume("i_bounded", "i < 1000000");
    // Invariant: even + odd == i
    ctx.push_assume("inv_ih", "even_count + odd_count == i");
    // Exactly one accumulator increments
    ctx.push_assume("is_even_bool", "elem_is_even == 0 || elem_is_even == 1");
    ctx.push_assume(
        "even_update",
        "(elem_is_even == 1 && even_new == even_count + 1 && odd_new == odd_count) || (elem_is_even == 0 && odd_new == odd_count + 1 && even_new == even_count)",
    );
    ctx.push_assume("i_step", "i_new == i + 1");

    ctx.push_assert("inv_preserved", "even_new + odd_new == i_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14d: two-accumulator sum invariant should verify, got: {:?}",
        result,
    );
}

/// Tier 14d: Two accumulators — exit VC establishes postcondition.
/// At exit: loop counter reached n, so even + odd == n.
/// BV overflow guard: n < 1000000 prevents wraparound counterexamples.
#[test]
fn test_vt_tier14d_two_accumulators_exit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("even_count", "u64");
    ctx.declare_var_parsed("odd_count", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("n", "u64");

    // BV overflow guard (Tier 13 lesson: mandatory for u64 reasoning)
    ctx.push_assume("n_bounded", "n < 1000000");
    // Loop invariant: even + odd == i, and both <= i
    ctx.push_assume("inv_sum", "even_count + odd_count == i");
    ctx.push_assume("even_le_i", "even_count <= i");
    ctx.push_assume("odd_le_i", "odd_count <= i");
    // Exit condition: i == n
    ctx.push_assume("exit_cond", "i == n");

    // Postcondition: even + odd == n and both bounded
    ctx.push_assert("post_sum", "even_count + odd_count == n");
    ctx.push_assert("even_bounded", "even_count <= n");
    ctx.push_assert("odd_bounded", "odd_count <= n");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14d: two-accumulator exit VC should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Sequence reversal (competition pattern)
//
// Reverse is a common sub-problem in VerifyThis (e.g., reverse a rope,
// reverse a persistent array). The invariant relates positions in the
// original and reversed sequences.
// ========================================================================

/// Tier 14e: Reversal postcondition — s_rev[k] == s[n-1-k] for concrete n=3.
#[test]
fn test_vt_tier14e_reverse_postcondition_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_rev", "Seq<i32>");

    ctx.push_assume("len_s", "s.len() == 3");
    ctx.push_assume("len_rev", "s_rev.len() == 3");
    ctx.push_assume("rev_0", "s_rev.index(0) == s.index(2)");
    ctx.push_assume("rev_1", "s_rev.index(1) == s.index(1)");
    ctx.push_assume("rev_2", "s_rev.index(2) == s.index(0)");

    ctx.push_assert(
        "endpoints_sum_preserved",
        "s_rev.index(0) + s_rev.index(2) == s.index(0) + s.index(2)",
    );
    ctx.push_assert(
        "all_positions_preserve_sum",
        "s_rev.index(0) + s_rev.index(1) + s_rev.index(2) == s.index(0) + s.index(1) + s.index(2)",
    );
    ctx.push_assert("len_preserved", "s_rev.len() == s.len()");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 14e: concrete reverse postcondition should verify, got: {:?}",
        result,
    );
}

/// Tier 14e: Reversal soundness negative — reversed sequence is not equal to original.
#[test]
fn test_vt_tier14e_reverse_not_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_rev", "Seq<i32>");

    ctx.push_assume("len_s", "s.len() == 3");
    ctx.push_assume("len_rev", "s_rev.len() == 3");
    ctx.push_assume("rev_0", "s_rev.index(0) == s.index(2)");
    ctx.push_assume("rev_1", "s_rev.index(1) == s.index(1)");
    ctx.push_assume("rev_2", "s_rev.index(2) == s.index(0)");

    // WRONG: reversed sequence is not generally s[0] == s_rev[0]
    ctx.push_assert("wrong_identity", "s.index(0) == s_rev.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 14e SOUNDNESS: reverse-not-identity (e.g. s=[1,2,3]) should produce a counterexample, got: {:?}",
        result,
    );
}
