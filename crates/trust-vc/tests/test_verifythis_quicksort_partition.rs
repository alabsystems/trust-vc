// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 50 — Quicksort Partition (Lomuto scheme) VCs.
//!
//! Lomuto partition: scan [lo, hi), swap elements <= pivot to front,
//! then swap pivot from hi to position i.
//!
//! Loop invariant:
//!   P1: forall k in [lo, i): s[k] <= pivot  (left)
//!   P2: forall k in [i, j): s[k] > pivot    (right)
//!   P3: s[hi] == pivot
//!
//! GROUP A: Init  B: Swap branch  C: No-swap  D: Exit  E: Concrete+negative
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

fn assume_seq_i64(ctx: &mut VerificationContext, name: &str, values: &[i64]) {
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", values.len()),
    );
    for (index, value) in values.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {value}"),
        );
    }
}

// ========================================================================
// GROUP A: Init — i = lo, j = lo, both partitions empty
// ========================================================================

/// Tier 50a: Init — i=lo, j=lo, partitions [lo,lo) and [lo,lo) are vacuous.
#[test]
fn test_vt_tier50a_partition_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("pivot", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("lo_lt_hi", "lo < hi");
    ctx.push_assume("hi_lt_n", "hi < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("pivot_def", "pivot == s.index(hi)");
    ctx.push_assume("i_init", "i == lo");
    ctx.push_assume("j_init", "j == lo");

    // P1: forall k in [lo, i): s[k] <= pivot — vacuously true (i == lo)
    ctx.push_assert(
        "left_vacuous",
        "forall(|k: u64| !(k >= lo && k < i) || s.index(k) <= pivot)",
    );
    // P2: forall k in [i, j): s[k] > pivot — vacuously true (i == j)
    ctx.push_assert(
        "right_vacuous",
        "forall(|k: u64| !(k >= i && k < j) || s.index(k) > pivot)",
    );
    // P3: pivot untouched
    ctx.push_assert("pivot_intact", "s.index(hi) == pivot");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50a: partition init should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step (swap branch) — s[j] <= pivot
// ========================================================================

/// Tier 50b: Swap branch — s[j] <= pivot → swap(i,j), i++, j++.
/// s_new[i] = s[j] <= pivot, so left region [lo, i+1) gains one element.
#[test]
fn test_vt_tier50b_swap_branch_left_grows() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("pivot", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("lo_le_i", "lo <= i");
    ctx.push_assume("i_le_j", "i <= j");
    ctx.push_assume("j_lt_hi", "j < hi");
    ctx.push_assume("hi_lt_n", "hi < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("pivot_def", "pivot == s.index(hi)");

    // IH: P1 — left region [lo, i) all <= pivot
    ctx.push_assume(
        "ih_left",
        "forall(|k: u64| !(k >= lo && k < i) || s.index(k) <= pivot)",
    );
    // Branch condition: s[j] <= pivot
    ctx.push_assume("branch_le", "s.index(j) <= pivot");
    // Swap effect: s_new[i] = s[j], s_new[j] = s[i]
    ctx.push_assume("swap_i", "s_new.index(i) == s.index(j)");

    // Assert: s_new[i] <= pivot (the swapped-in element is in left region)
    ctx.push_assert("new_elem_le_pivot", "s_new.index(i) <= pivot");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50b: swap branch left element should verify, got: {:?}",
        result,
    );
}

/// Tier 50b: Swap branch frame — swap at (i,j) preserves [lo, i).
#[test]
fn test_vt_tier50b_swap_branch_frame() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("pivot", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("lo_le_i", "lo <= i");
    ctx.push_assume("i_le_j", "i <= j");
    ctx.push_assume("j_lt_hi", "j < hi");
    ctx.push_assume("hi_lt_n", "hi < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("pivot_def", "pivot == s.index(hi)");

    // IH: P1 holds for original s
    ctx.push_assume(
        "ih_left",
        "forall(|k: u64| !(k >= lo && k < i) || s.index(k) <= pivot)",
    );
    // Frame: swap only touches i and j, not [lo, i)
    ctx.push_assume(
        "frame",
        "forall(|k: u64| !(k >= lo && k < i) || s_new.index(k) == s.index(k))",
    );

    // P1 preserved in s_new for [lo, i)
    ctx.push_assert(
        "left_preserved",
        "forall(|k: u64| !(k >= lo && k < i) || s_new.index(k) <= pivot)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50b: swap branch frame should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Step (no-swap branch) — s[j] > pivot
// ========================================================================

/// Tier 50c: No-swap branch — s[j] > pivot, j++. Right region grows.
#[test]
fn test_vt_tier50c_no_swap_right_grows() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("pivot", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("lo_le_i", "lo <= i");
    ctx.push_assume("i_le_j", "i <= j");
    ctx.push_assume("j_lt_hi", "j < hi");
    ctx.push_assume("hi_lt_n", "hi < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("pivot_def", "pivot == s.index(hi)");

    // IH: P2 for [i, j)
    ctx.push_assume(
        "ih_right",
        "forall(|k: u64| !(k >= i && k < j) || s.index(k) > pivot)",
    );
    // Branch condition: s[j] > pivot
    ctx.push_assume("branch_gt", "s.index(j) > pivot");

    // P2 extended to [i, j+1)
    ctx.push_assert(
        "right_extended",
        "forall(|k: u64| !(k >= i && k < j + 1) || s.index(k) > pivot)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50c: no-swap branch right grows should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Exit — final swap places pivot at partition boundary
// ========================================================================

/// Tier 50d: Final swap — swap(i, hi) places pivot; left region <= pivot.
#[test]
fn test_vt_tier50d_final_swap_pivot_placed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("pivot", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("lo_le_i", "lo <= i");
    ctx.push_assume("i_le_hi", "i <= hi");
    ctx.push_assume("hi_lt_n", "hi < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("pivot_def", "pivot == s.index(hi)");

    // Loop invariant at exit (j == hi):
    ctx.push_assume(
        "inv_left",
        "forall(|k: u64| !(k >= lo && k < i) || s.index(k) <= pivot)",
    );
    // Final swap: s_new[i] = s[hi] = pivot
    ctx.push_assume("swap_i", "s_new.index(i) == s.index(hi)");
    // Frame: [lo, i) unchanged
    ctx.push_assume(
        "frame_left",
        "forall(|k: u64| !(k >= lo && k < i) || s_new.index(k) == s.index(k))",
    );

    // Q1: all elements left of pivot are <= pivot
    ctx.push_assert(
        "post_left",
        "forall(|k: u64| !(k >= lo && k < i) || s_new.index(k) <= s_new.index(i))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50d: final swap pivot placed should verify, got: {:?}",
        result,
    );
}

/// Tier 50d: Final swap — right region (i, hi] still > pivot.
#[test]
fn test_vt_tier50d_final_swap_right_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("pivot", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("lo_le_i", "lo <= i");
    ctx.push_assume("i_lt_hi", "i < hi");
    ctx.push_assume("hi_lt_n", "hi < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("pivot_def", "pivot == s.index(hi)");

    // P2: right region [i, hi) all > pivot
    ctx.push_assume(
        "inv_right",
        "forall(|k: u64| !(k >= i && k < hi) || s.index(k) > pivot)",
    );
    // Final swap: s_new[hi] = s[i], frame: (i, hi) unchanged
    ctx.push_assume("swap_hi", "s_new.index(hi) == s.index(i)");
    ctx.push_assume(
        "frame_mid",
        "forall(|k: u64| !(k > i && k < hi) || s_new.index(k) == s.index(k))",
    );

    // s[i] > pivot (from P2 with k=i) — the element moved to hi is > pivot
    ctx.push_assert("moved_gt_pivot", "s_new.index(hi) > pivot");
    // Right interior (i+1, hi) still > pivot
    ctx.push_assert(
        "mid_gt_pivot",
        "forall(|k: u64| !(k > i && k < hi) || s_new.index(k) > pivot)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50d: final swap right preserved should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Concrete trace + negative tests
// ========================================================================

/// Tier 50e: All-left — [3,1,4,1,5] pivot=5, all elements <= pivot.
#[test]
fn test_vt_tier50e_concrete_all_left() {
    let mut ctx = VerificationContext::new();
    // After partition: [3, 1, 4, 1, 5] — pivot 5 is largest, all go left.
    // Final state: [3, 1, 4, 1, 5] (unchanged since all <= pivot).
    assume_seq_i64(&mut ctx, "s", &[3, 1, 4, 1, 5]);

    // All elements at positions [0,4) are <= s[4]
    ctx.push_assert(
        "all_left",
        "forall(|k: u64| !(k < 4) || s.index(k) <= s.index(4))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50e: all-left concrete trace should verify, got: {:?}",
        result,
    );
}

/// Tier 50e: Mixed — [7,2,8,1,3] pivot=3, result [2,1,3,8,7].
#[test]
fn test_vt_tier50e_concrete_mixed_partition() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s_new", &[2, 1, 3, 8, 7]);

    // Left of pivot: [0, 2) all <= s_new[2]=3
    ctx.push_assert("left_0", "s_new.index(0) <= s_new.index(2)");
    ctx.push_assert("left_1", "s_new.index(1) <= s_new.index(2)");
    // Right of pivot: (2, 5] all > s_new[2]=3
    ctx.push_assert("right_3", "s_new.index(3) > s_new.index(2)");
    ctx.push_assert("right_4", "s_new.index(4) > s_new.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50e: mixed partition trace should verify, got: {:?}",
        result,
    );
}

/// Tier 50e: All-right — [5,4,3,2,1] pivot=1, result [1,4,3,2,5].
#[test]
fn test_vt_tier50e_concrete_all_right() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s_new", &[1, 4, 3, 2, 5]);

    // Pivot is at position 0 (i=0 after scan, then swap)
    // Right region (0, 4]: all > s_new[0]=1
    ctx.push_assert("right_1", "s_new.index(1) > s_new.index(0)");
    ctx.push_assert("right_2", "s_new.index(2) > s_new.index(0)");
    ctx.push_assert("right_3", "s_new.index(3) > s_new.index(0)");
    ctx.push_assert("right_4", "s_new.index(4) > s_new.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 50e: all-right concrete trace should verify, got: {:?}",
        result,
    );
}

/// Tier 50e NEGATIVE: Wrong claim — right region [i,hi) not all <= pivot.
#[test]
fn test_vt_tier50e_wrong_partition_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("pivot", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_eq_3", "n == 3");
    ctx.push_assume("lo_eq_0", "lo == 0");
    ctx.push_assume("hi_eq_2", "hi == 2");
    ctx.push_assume("i_eq_1", "i == 1");
    ctx.push_assume("lo_lt_hi", "lo < hi");
    ctx.push_assume("hi_lt_n", "hi < n");
    ctx.push_assume("n_ge3", "n >= 3");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("pivot_def", "pivot == s.index(hi)");
    ctx.push_assume("pivot_zero", "pivot == 0");
    ctx.push_assume("right_witness", "s.index(i) == 1");
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_le_hi", "i <= hi");

    // WRONG: the concrete witness at i is in the right region and exceeds pivot.
    ctx.push_assert("wrong_all_le", "s.index(i) <= pivot");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 50e SOUNDNESS: right region not all <= pivot, got: {:?}",
        result,
    );
}

/// Tier 50e NEGATIVE: s[0] != s[2] in [2,1,3,8,7] — wrong pivot position.
#[test]
fn test_vt_tier50e_wrong_pivot_position_negative() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[2, 1, 3, 8, 7]);

    // Pivot is at position 2, NOT position 0
    ctx.push_assert("wrong_pivot_pos", "s.index(0) == s.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 50e SOUNDNESS: wrong pivot position, got: {:?}",
        result,
    );
}
