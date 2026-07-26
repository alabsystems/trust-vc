// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 15 — Multi-sequence and merge VCs.
//!
//! Tests multi-sequence patterns from real VerifyThis problems:
//! merge (mergesort 2022), splitting, two-pointer, element provenance.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// GROUP A: Merge VCs (mergesort core — VerifyThis 2022)

/// Tier 15a: Merge init VC — empty output is vacuously sorted.
#[test]
fn test_vt_tier15a_merge_init_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("b", "Seq<i32>");
    ctx.declare_var_parsed("out", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("n_a", "u64");
    ctx.declare_var_parsed("n_b", "u64");

    ctx.push_assume("len_a", "a.len() == n_a");
    ctx.push_assume("len_b", "b.len() == n_b");
    ctx.push_assume("out_empty", "out.len() == 0");
    ctx.push_assume("i_init", "i == 0");
    ctx.push_assume("j_init", "j == 0");

    // Invariant: out is sorted (vacuously true for empty sequence)
    ctx.push_assert(
        "out_sorted_vacuous",
        "forall(|k: u64| !(k + 1 < out.len()) || out.index(k) <= out.index(k + 1))",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15a: merge init VC (empty output) should verify, got: {:?}",
        result,
    );
}

/// Tier 15a: Merge step — appending element >= last preserves sortedness.
#[test]
fn test_vt_tier15a_merge_step_append_sorted() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("v0", "i32");
    ctx.declare_var_parsed("v1", "i32");
    ctx.declare_var_parsed("v_new", "i32");

    // Existing output is sorted: v0 <= v1
    ctx.push_assume("out_sorted", "v0 <= v1");
    // New element from merge: v_new >= v1 (we picked the min of heads)
    ctx.push_assume("new_ge_last", "v_new >= v1");

    // Verify: boundary is sorted
    ctx.push_assert("sorted_boundary", "v1 <= v_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15a: merge step append should verify, got: {:?}",
        result,
    );
}

/// Tier 15a: Merge exit VC — output length equals sum of input lengths.
/// BV overflow guard: n_a, n_b < 500000 prevents sum wraparound.
#[test]
fn test_vt_tier15a_merge_exit_length() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("out_len", "u64");
    ctx.declare_var_parsed("n_a", "u64");
    ctx.declare_var_parsed("n_b", "u64");

    ctx.push_assume("n_a_bounded", "n_a < 500000");
    ctx.push_assume("n_b_bounded", "n_b < 500000");
    // Loop invariant: out_len == i + j (each step advances one pointer)
    ctx.push_assume("inv_len", "out_len == i + j");
    // Exit: both inputs exhausted
    ctx.push_assume("i_done", "i == n_a");
    ctx.push_assume("j_done", "j == n_b");

    ctx.push_assert("total_len", "out_len == n_a + n_b");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15a: merge exit length should verify, got: {:?}",
        result,
    );
}

/// Tier 15a: Merge negative — skipping smaller head breaks min property.
#[test]
fn test_vt_tier15a_merge_negative_skip_smaller() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("b", "Seq<i32>");
    ctx.declare_var_parsed("out_first", "i32");

    ctx.push_assume("a_len", "a.len() == 1");
    ctx.push_assume("b_len", "b.len() == 1");
    ctx.push_assume("a_val", "a.index(0) == 1");
    ctx.push_assume("b_val", "b.index(0) == 5");
    // Wrong: took b[0] instead of a[0]
    ctx.push_assume("wrong_pick", "out_first == b.index(0)");

    // WRONG: out_first <= a[0] (i.e., 5 <= 1)
    ctx.push_assert("wrong_min", "out_first <= a.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 15a SOUNDNESS: skipping smaller element (out_first=5 vs a[0]=1) should produce a counterexample, got: {:?}",
        result,
    );
}

// GROUP B: Sequence splitting / disjoint regions

/// Tier 15b: Split — [0, mid) and [mid, n) cover all of [0, n).
#[test]
fn test_vt_tier15b_split_coverage() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("k", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("mid_valid", "mid <= n");
    ctx.push_assume("k_in_range", "k < n");

    // Any k < n is either in [0, mid) or [mid, n)
    ctx.push_assert("covers", "k < mid || k >= mid");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15b: split coverage should verify, got: {:?}",
        result,
    );
}

/// Tier 15b: Split — sorted halves + boundary implies globally sorted (n=4).
#[test]
fn test_vt_tier15b_split_sorted_halves_boundary() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 4");
    // Left half sorted
    ctx.push_assume("left_sorted", "s.index(0) <= s.index(1)");
    // Right half sorted
    ctx.push_assume("right_sorted", "s.index(2) <= s.index(3)");
    // Boundary: last of left <= first of right
    ctx.push_assume("boundary", "s.index(1) <= s.index(2)");

    ctx.push_assert("sorted_02", "s.index(0) <= s.index(2)");
    ctx.push_assert("sorted_03", "s.index(0) <= s.index(3)");
    ctx.push_assert("sorted_13", "s.index(1) <= s.index(3)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15b: split sorted halves + boundary should verify, got: {:?}",
        result,
    );
}

/// Tier 15b: Split soundness negative — sorted halves without boundary.
/// Two individually sorted halves are NOT globally sorted without boundary condition.
#[test]
fn test_vt_tier15b_split_negative_no_boundary() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("mid", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_eq3", "n == 3");
    ctx.push_assume("mid_eq2", "mid == 2");
    // Left half sorted: s[0] <= s[1]
    ctx.push_assume("left_sorted", "s.index(0) <= s.index(1)");
    // Right half: just s[2] (trivially sorted)
    // NO boundary condition

    // WRONG: claiming global sortedness without boundary
    ctx.push_assert("wrong_global", "s.index(1) <= s.index(2)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 15b SOUNDNESS: sorted halves without boundary (e.g. s=[0,10,0]) should produce a counterexample, got: {:?}",
        result,
    );
}

// GROUP C: Two-pointer synchronization (merge, intersection, difference)

/// Tier 15c: Two-pointer merge — pointer advance preserves coverage.
/// i advances on a, j on b, and i+j increases by exactly 1 each step.
#[test]
fn test_vt_tier15c_two_pointer_advance_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("j_new", "u64");
    ctx.declare_var_parsed("n_a", "u64");
    ctx.declare_var_parsed("n_b", "u64");

    ctx.push_assume("i_bounded", "i < 500000");
    ctx.push_assume("j_bounded", "j < 500000");
    // Guard: at least one input not exhausted
    ctx.push_assume("guard", "i < n_a || j < n_b");
    // Exactly one pointer advances
    ctx.push_assume(
        "one_advances",
        "(i_new == i + 1 && j_new == j) || (i_new == i && j_new == j + 1)",
    );

    // Total progress: i_new + j_new == i + j + 1
    ctx.push_assert("progress", "i_new + j_new == i + j + 1");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15c: two-pointer advance should verify, got: {:?}",
        result,
    );
}

/// Tier 15c: Two-pointer — exhaustion implies total coverage.
/// When both i == n_a and j == n_b, total processed == n_a + n_b.
#[test]
fn test_vt_tier15c_two_pointer_exhaustion() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("out_len", "u64");
    ctx.declare_var_parsed("n_a", "u64");
    ctx.declare_var_parsed("n_b", "u64");

    ctx.push_assume("n_a_bounded", "n_a < 500000");
    ctx.push_assume("n_b_bounded", "n_b < 500000");
    ctx.push_assume("inv", "out_len == i + j");
    ctx.push_assume("a_done", "i == n_a");
    ctx.push_assume("b_done", "j == n_b");

    ctx.push_assert("total", "out_len == n_a + n_b");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15c: two-pointer exhaustion should verify, got: {:?}",
        result,
    );
}

/// Tier 15c: Two-pointer soundness negative — both advance simultaneously.
/// If both pointers advance, total increases by 2 (not 1).
#[test]
fn test_vt_tier15c_two_pointer_negative_double_advance() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("j_new", "u64");

    ctx.push_assume("i_bounded", "i < 500000");
    ctx.push_assume("j_bounded", "j < 500000");
    // WRONG: both advance
    ctx.push_assume("both_advance", "i_new == i + 1 && j_new == j + 1");

    // Claiming total progress is 1 (but it's actually 2)
    ctx.push_assert("wrong_progress", "i_new + j_new == i + j + 1");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 15c SOUNDNESS: double advance yields progress 2 (not 1), should produce a counterexample, got: {:?}",
        result,
    );
}

// GROUP D: Element preservation (per-position provenance)

/// Tier 15d: Element provenance — merge a=[1,3], b=[2,4] → out=[1,2,3,4].
#[test]
fn test_vt_tier15d_element_provenance_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("b", "Seq<i32>");
    ctx.declare_var_parsed("out", "Seq<i32>");

    ctx.push_assume("a_len", "a.len() == 2");
    ctx.push_assume("b_len", "b.len() == 2");
    ctx.push_assume("out_len", "out.len() == 4");
    // Concrete values
    ctx.push_assume("a0", "a.index(0) == 1");
    ctx.push_assume("a1", "a.index(1) == 3");
    ctx.push_assume("b0", "b.index(0) == 2");
    ctx.push_assume("b1", "b.index(1) == 4");
    // Merged output
    ctx.push_assume("o0", "out.index(0) == 1");
    ctx.push_assume("o1", "out.index(1) == 2");
    ctx.push_assume("o2", "out.index(2) == 3");
    ctx.push_assume("o3", "out.index(3) == 4");

    // Verify: output is sorted
    ctx.push_assert("sorted_01", "out.index(0) <= out.index(1)");
    ctx.push_assert("sorted_12", "out.index(1) <= out.index(2)");
    ctx.push_assert("sorted_23", "out.index(2) <= out.index(3)");

    // Verify: each output element exists in some input
    ctx.push_assert(
        "prov_0",
        "out.index(0) == a.index(0) || out.index(0) == a.index(1) || out.index(0) == b.index(0) || out.index(0) == b.index(1)",
    );
    ctx.push_assert(
        "prov_3",
        "out.index(3) == a.index(0) || out.index(3) == a.index(1) || out.index(3) == b.index(0) || out.index(3) == b.index(1)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15d: concrete element provenance should verify, got: {:?}",
        result,
    );
}

/// Tier 15d: Element provenance negative — output has element not in either input.
#[test]
fn test_vt_tier15d_element_provenance_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("b", "Seq<i32>");
    ctx.declare_var_parsed("out", "Seq<i32>");

    ctx.push_assume("a_len", "a.len() == 1");
    ctx.push_assume("b_len", "b.len() == 1");
    ctx.push_assume("out_len", "out.len() == 2");
    // Concrete: a=[5], b=[10]
    ctx.push_assume("a0", "a.index(0) == 5");
    ctx.push_assume("b0", "b.index(0) == 10");

    // WRONG: claiming out[0] == 7 (which is not in either input)
    ctx.push_assume("out0_wrong", "out.index(0) == 7");
    ctx.push_assert(
        "prov_wrong",
        "out.index(0) == a.index(0) || out.index(0) == b.index(0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 15d SOUNDNESS: out[0]=7 not in a=[5],b=[10] should produce a counterexample, got: {:?}",
        result,
    );
}

// GROUP E: Merge-sort end-to-end VCs

/// Tier 15e: Mergesort — sorted halves [1,4] and [2,5] merge to [1,2,4,5].
#[test]
fn test_vt_tier15e_mergesort_sorted_halves_merge() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("b", "Seq<i32>");
    ctx.declare_var_parsed("out", "Seq<i32>");

    // a = [1, 4], b = [2, 5], sorted
    ctx.push_assume("a_len", "a.len() == 2");
    ctx.push_assume("b_len", "b.len() == 2");
    ctx.push_assume("a0", "a.index(0) == 1");
    ctx.push_assume("a1", "a.index(1) == 4");
    ctx.push_assume("b0", "b.index(0) == 2");
    ctx.push_assume("b1", "b.index(1) == 5");
    ctx.push_assume("a_sorted", "a.index(0) <= a.index(1)");
    ctx.push_assume("b_sorted", "b.index(0) <= b.index(1)");

    // Merge: take min heads iteratively → [1, 2, 4, 5]
    ctx.push_assume("out_len", "out.len() == 4");
    ctx.push_assume("o0", "out.index(0) == 1");
    ctx.push_assume("o1", "out.index(1) == 2");
    ctx.push_assume("o2", "out.index(2) == 4");
    ctx.push_assume("o3", "out.index(3) == 5");

    // Verify: merged output is sorted
    ctx.push_assert("s01", "out.index(0) <= out.index(1)");
    ctx.push_assert("s12", "out.index(1) <= out.index(2)");
    ctx.push_assert("s23", "out.index(2) <= out.index(3)");
    // Verify: length preserved
    ctx.push_assert("len_sum", "out.len() == a.len() + b.len()");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15e: mergesort decomposition should verify, got: {:?}",
        result,
    );
}

/// Tier 15e: Mergesort — picking min(a[i], b[j]) preserves output sortedness.
#[test]
fn test_vt_tier15e_mergesort_symbolic_merge_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("b", "Seq<i32>");
    ctx.declare_var_parsed("out_last", "i32");
    ctx.declare_var_parsed("picked", "i32");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");

    // Both inputs sorted (relevant elements)
    ctx.push_assume("a_len", "a.len() == 2");
    ctx.push_assume("b_len", "b.len() == 2");
    ctx.push_assume("i_step", "i == 1");
    ctx.push_assume("j_step", "j == 1");
    ctx.push_assume("a_sorted_at_i", "a.index(0) <= a.index(i)");
    ctx.push_assume("b_sorted_at_j", "b.index(0) <= b.index(j)");
    // out_last came from a[i-1] or b[j-1] (the previous pick)
    ctx.push_assume(
        "out_last_source",
        "out_last == a.index(0) || out_last == b.index(0)",
    );
    // We pick the smaller of a[i], b[j]
    ctx.push_assume("pick_min", "picked <= a.index(i) && picked <= b.index(j)");
    ctx.push_assume(
        "pick_is_one",
        "picked == a.index(i) || picked == b.index(j)",
    );
    // The previous pick was <= both current heads
    // (because inputs are sorted and we always pick the min)
    ctx.push_assume("out_last_le_ai", "out_last <= a.index(i)");
    ctx.push_assume("out_last_le_bj", "out_last <= b.index(j)");

    // Verify: picked >= out_last (output remains sorted)
    ctx.push_assert("sorted_step", "picked >= out_last");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 15e: symbolic merge step should verify, got: {:?}",
        result,
    );
}
