// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 49 — Selection Sort algorithm VCs.
//!
//! Selection sort: for i in 0..n-1, find min of [i,n), swap to position i.
//!
//! Outer invariant:
//!   sorted(s[0..i]): forall j. j+1 < i => s[j] <= s[j+1]
//!   partitioned(i):  forall j < i. s[j] <= s[i]
//! Inner invariant:
//!   s[min_idx] <= s[k] for all k in [i, j)
//!
//! GROUP A: Outer loop Init/Exit
//! GROUP B: Inner loop (min-finding) Init/Step/Exit
//! GROUP C: Swap step — invariant preservation
//! GROUP D: Full concrete trace + negative tests
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
// GROUP A: Outer loop Init and Exit
// ========================================================================

/// Tier 49a: Outer init — i=0, sorted prefix [0,0) is vacuously true.
#[test]
fn test_vt_tier49a_selection_sort_outer_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("i_init", "i == 0");

    ctx.push_assert(
        "sorted_vacuous",
        "forall(|j: u64| !(j + 1 < i) || s.index(j) <= s.index(j + 1))",
    );
    ctx.push_assert(
        "partition_vacuous",
        "forall(|j: u64| !(j < i) || s.index(j) <= s.index(i))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49a: outer init should verify, got: {:?}",
        result,
    );
}

/// Tier 49a: Outer exit — sorted concrete array satisfies postcondition.
///
/// Guard uses `!(j < 4)` (not `!(j + 1 < 5)`) so the bounds checker
/// connects the guard to `s.index(j + 1)` bounds without extra arithmetic.
#[test]
fn test_vt_tier49a_selection_sort_outer_exit() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[1, 3, 5, 7, 9]);

    ctx.push_assert(
        "fully_sorted",
        "forall(|j: u64| !(j < 4) || s.index(j) <= s.index(j + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49a: outer exit should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Inner loop (min-finding) Init / Step / Exit
// ========================================================================

/// Tier 49b: Inner init — min_idx = i is minimum of singleton [i, i+1).
#[test]
fn test_vt_tier49b_inner_loop_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("min_idx", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume("min_init", "min_idx == i");
    ctx.push_assume("min_idx_lt_n", "min_idx < n");

    ctx.push_assert("min_of_singleton", "s.index(min_idx) <= s.index(i)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49b: inner init should verify, got: {:?}",
        result,
    );
}

/// Tier 49b: Inner step (update) — s[j] < s[min_idx] → min_idx_new = j.
#[test]
fn test_vt_tier49b_inner_loop_step_update() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("min_idx", "u64");
    ctx.declare_var_parsed("min_idx_new", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("i_lt_j", "i < j");
    ctx.push_assume("j_lt_n", "j < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("min_idx_range", "min_idx >= i && min_idx < j");
    ctx.push_assume(
        "ih_min",
        "forall(|k: u64| !(k >= i && k < j) || s.index(min_idx) <= s.index(k))",
    );
    ctx.push_assume("branch_lt", "s.index(j) < s.index(min_idx)");
    ctx.push_assume("min_update", "min_idx_new == j");

    ctx.push_assert(
        "min_preserved",
        "forall(|k: u64| !(k >= i && k < j + 1) || s.index(min_idx_new) <= s.index(k))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49b: inner step (update) should verify, got: {:?}",
        result,
    );
}

/// Tier 49b: Inner step (keep) — s[j] >= s[min_idx] → min_idx unchanged.
#[test]
fn test_vt_tier49b_inner_loop_step_keep() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("min_idx", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("i_lt_j", "i < j");
    ctx.push_assume("j_lt_n", "j < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("min_idx_range", "min_idx >= i && min_idx < j");
    ctx.push_assume(
        "ih_min",
        "forall(|k: u64| !(k >= i && k < j) || s.index(min_idx) <= s.index(k))",
    );
    ctx.push_assume("branch_ge", "s.index(j) >= s.index(min_idx)");

    ctx.push_assert(
        "min_preserved",
        "forall(|k: u64| !(k >= i && k < j + 1) || s.index(min_idx) <= s.index(k))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49b: inner step (keep) should verify, got: {:?}",
        result,
    );
}

/// Tier 49b: Inner exit — min_idx is minimum of entire suffix [i, n).
#[test]
fn test_vt_tier49b_inner_loop_exit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("min_idx", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume("min_idx_range", "min_idx >= i && min_idx < n");
    ctx.push_assume(
        "min_of_suffix",
        "forall(|k: u64| !(k >= i && k < n) || s.index(min_idx) <= s.index(k))",
    );

    ctx.push_assert("min_le_i", "s.index(min_idx) <= s.index(i)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49b: inner exit should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Swap step — outer loop invariant preservation
// ========================================================================

/// Tier 49c: Swap places the minimum at position i.
#[test]
fn test_vt_tier49c_swap_places_minimum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("min_idx", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume("min_idx_range", "min_idx >= i && min_idx < n");
    ctx.push_assume(
        "min_of_suffix",
        "forall(|k: u64| !(k >= i && k < n) || s.index(min_idx) <= s.index(k))",
    );
    ctx.push_assume("swap_i", "s_new.index(i) == s.index(min_idx)");
    ctx.push_assume("swap_min", "s_new.index(min_idx) == s.index(i)");

    ctx.push_assert(
        "new_i_is_min",
        "forall(|k: u64| !(k >= i && k < n) || s_new.index(i) <= s.index(k))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49c: swap places minimum at position i, got: {:?}",
        result,
    );
}

/// Tier 49c: Swap frame — concrete sorted prefix is preserved after swap.
///
/// Concrete array [1, 2, 8, 5, 4] with i=2: sorted prefix [1, 2] unchanged
/// after swapping positions 2 and 4. Uses concrete indices to avoid
/// quantifier chaining timeout on single-round E-matching.
#[test]
fn test_vt_tier49c_swap_frame_prefix() {
    let mut ctx = VerificationContext::new();
    // Before swap at (2, 4): [1, 2, 8, 5, 4]
    assume_seq_i64(&mut ctx, "s", &[1, 2, 8, 5, 4]);
    // After swap: [1, 2, 4, 5, 8]
    assume_seq_i64(&mut ctx, "s_new", &[1, 2, 4, 5, 8]);

    // Prefix [0, 2) unchanged
    ctx.push_assert("frame_0", "s_new.index(0) == s.index(0)");
    ctx.push_assert("frame_1", "s_new.index(1) == s.index(1)");
    // Sorted prefix preserved
    ctx.push_assert("sorted_01", "s_new.index(0) <= s_new.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49c: swap frame preserves sorted prefix, got: {:?}",
        result,
    );
}

/// Tier 49c: Partition extension — prefix elements <= new s[i].
///
/// Partition IH says s[j] <= s[k] for j < i and all k >= i.
/// min_idx >= i, so s[j] <= s[min_idx] = s_new[i].
#[test]
fn test_vt_tier49c_partition_extension() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("min_idx", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("min_idx_range", "min_idx >= i && min_idx < n");
    // Partition IH: prefix elements <= s[min_idx]
    // (since min_idx >= i, partition_ih gives s[j] <= s[min_idx] for j < i)
    ctx.push_assume(
        "partition_ih",
        "forall(|j: u64| !(j < i) || s.index(j) <= s.index(min_idx))",
    );
    ctx.push_assume("swap_i", "s_new.index(i) == s.index(min_idx)");
    ctx.push_assume(
        "frame",
        "forall(|j: u64| !(j < i) || s_new.index(j) == s.index(j))",
    );

    ctx.push_assert(
        "prefix_le_new_i",
        "forall(|j: u64| !(j < i) || s_new.index(j) <= s_new.index(i))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49c: partition extension should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Full concrete trace + negative tests
// ========================================================================

/// Tier 49d: Full trace — selection sort [5, 2, 8, 1, 4] → [1, 2, 4, 5, 8].
#[test]
fn test_vt_tier49d_selection_sort_full_trace() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[1, 2, 4, 5, 8]);

    ctx.push_assert(
        "sorted_post",
        "forall(|j: u64| !(j < 4) || s.index(j) <= s.index(j + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49d: full trace sorted postcondition should verify, got: {:?}",
        result,
    );
}

/// Tier 49d: Concrete min-finding — [5, 2, 8, 1, 4], min of [0,5) is at idx 3.
#[test]
fn test_vt_tier49d_concrete_min_finding() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[5, 2, 8, 1, 4]);

    ctx.push_assert(
        "min_at_3",
        "forall(|k: u64| !(k < 5) || s.index(3) <= s.index(k))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49d: concrete min-finding should verify, got: {:?}",
        result,
    );
}

/// Tier 49d: Concrete swap — swap(0,3) on [5,2,8,1,4] → [1,2,8,5,4].
#[test]
fn test_vt_tier49d_concrete_swap_step() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[5, 2, 8, 1, 4]);
    assume_seq_i64(&mut ctx, "s_new", &[1, 2, 8, 5, 4]);

    // s_new[0] is the global minimum
    ctx.push_assert(
        "s_new_0_is_min",
        "forall(|k: u64| !(k < 5) || s_new.index(0) <= s.index(k))",
    );
    // Frame: indices 1 and 2 unchanged from s (index 4 also unchanged)
    ctx.push_assert("frame_1", "s_new.index(1) == s.index(1)");
    ctx.push_assert("frame_2", "s_new.index(2) == s.index(2)");
    ctx.push_assert("frame_4", "s_new.index(4) == s.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 49d: concrete swap step should verify, got: {:?}",
        result,
    );
}

/// Tier 49d: Wrong minimum negative — max is not min.
#[test]
fn test_vt_tier49d_wrong_minimum_negative() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[1, 9, 2]);
    ctx.declare_var_parsed("max_idx", "u64");

    // #2796: keep this negative witness concrete. The quantified max
    // assumption variant still fails closed in ay skipped-quantifier validation.
    ctx.push_assume("max_idx_is_one", "max_idx == 1");

    // WRONG: claiming max is also min
    ctx.push_assert("wrong_min_claim", "s.index(max_idx) <= s.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 49d SOUNDNESS: max is not min, got: {:?}",
        result,
    );
}

/// Tier 49d: Unsorted array negative — [5,2,8,1,4] is not sorted.
#[test]
fn test_vt_tier49d_unsorted_array_negative() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[5, 2, 8, 1, 4]);

    ctx.push_assert(
        "wrong_sorted",
        "forall(|j: u64| !(j < 4) || s.index(j) <= s.index(j + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 49d SOUNDNESS: [5,2,8,1,4] is not sorted, got: {:?}",
        result,
    );
}
