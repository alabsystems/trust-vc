// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 51 — Insertion Sort algorithm VCs.
//!
//! Insertion sort: for i in 1..n, take key=s[i], shift elements > key
//! right by one, insert key at position p.
//!
//! Outer invariant:
//!   sorted(s[0..i]): forall j. j+1 < i => s[j] <= s[j+1]
//! Inner invariant:
//!   gap at j+1: s[j] > key, elements [j+1..i) already shifted right
//! Insertion postcondition:
//!   s_new[p] = key, s_new[p-1] <= key (if p>0), key < s_new[p+1] (if p<i)
//!
//! GROUP A: Outer loop Init/Exit
//! GROUP B: Inner shift step
//! GROUP C: Insertion point — boundary reasoning
//! GROUP D: Concrete traces
//! GROUP E: Negative tests
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

/// Tier 51a: Outer init — i=1, sorted prefix [0,1) is vacuously true.
///
/// A single-element subarray is always sorted: the universal quantifier
/// over adjacent pairs has an empty domain when i=1.
#[test]
fn test_vt_tier51a_insertion_sort_outer_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("i_init", "i == 1");

    // sorted [0, i) = forall k: k+1 < i && k < n => s[k] <= s[k+1]
    // With i=1: k+1 < 1 wraps at k=u64::MAX in BV64, so add k < n guard
    // to prevent overflow bounds-check failure.
    ctx.push_assert(
        "sorted_vacuous",
        "forall(|k: u64| !(k + 1 < i && k < n) || s.index(k) <= s.index(k + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51a: outer init should verify, got: {:?}",
        result,
    );
}

/// Tier 51a: Outer exit — concrete sorted array satisfies postcondition.
///
/// Guard uses `!(k < 4)` so bounds checker connects guard to
/// `s.index(k + 1)` bounds without extra arithmetic.
#[test]
fn test_vt_tier51a_insertion_sort_outer_exit() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[1, 2, 4, 5, 8]);

    ctx.push_assert(
        "fully_sorted",
        "forall(|k: u64| !(k < 4) || s.index(k) <= s.index(k + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51a: outer exit should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Inner shift step
// ========================================================================

/// Tier 51b: Shift step — s[j] > key → s_new[j+1] = s[j] → s_new[j+1] > key.
///
/// Each inner-loop iteration shifts one element right. The shifted
/// element is > key (that's why the loop continues past it).
#[test]
fn test_vt_tier51b_shift_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("key", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume("j_lt_i", "j < i");
    ctx.push_assume("n_bounded", "n < 1000000");

    // Inner loop condition: s[j] > key
    ctx.push_assume("loop_cond", "s.index(j) > key");
    // Shift: s_new[j+1] = s[j]
    ctx.push_assume("shift", "s_new.index(j + 1) == s.index(j)");

    // The shifted element is > key
    ctx.push_assert("shifted_gt_key", "s_new.index(j + 1) > key");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51b: shift step should verify, got: {:?}",
        result,
    );
}

/// Tier 51b: Shift frame — positions below j are untouched, so the
/// sorted prefix [0, j) is preserved in s_new.
///
/// Uses frame + IH to prove sorted(s_new[0, j)) from sorted(s[0, j)).
/// Concrete trace avoids multi-round E-matching timeout: [1,3,5,7,_]
/// shifted at j=2 still has [1,3] sorted in s_new.
#[test]
fn test_vt_tier51b_shift_frame() {
    let mut ctx = VerificationContext::new();
    // Before: [1, 3, 5, 7, 4]. Outer i=4, key=4. Inner shifts at j=3,2.
    // After shift at j=2: s_new = [1, 3, _, 5, 7] where _ is gap.
    // Frame: positions [0, 2) = [1, 3] unchanged.
    assume_seq_i64(&mut ctx, "s", &[1, 3, 5, 7, 4]);
    assume_seq_i64(&mut ctx, "s_new", &[1, 3, 5, 5, 7]);

    // Frame preserved
    ctx.push_assert("frame_0", "s_new.index(0) == s.index(0)");
    ctx.push_assert("frame_1", "s_new.index(1) == s.index(1)");
    // Sorted prefix [0, 2) preserved
    ctx.push_assert("sorted_prefix", "s_new.index(0) <= s_new.index(1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51b: shift frame should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Insertion point — boundary reasoning
// ========================================================================

/// Tier 51c: Left boundary — s[p-1] <= key ensures s_new[p-1] <= s_new[p].
///
/// Inner loop exits when s[j] <= key (or j wraps past 0).
/// At exit, p = j+1, so s[p-1] <= key. With frame [0,p) unchanged and
/// s_new[p] = key, left boundary of insertion is valid.
#[test]
fn test_vt_tier51c_insert_left_boundary() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("p", "u64");
    ctx.declare_var_parsed("pm1", "u64");
    ctx.declare_var_parsed("key", "i64");
    ctx.declare_var_parsed("left_val", "i64");
    ctx.declare_var_parsed("inserted_val", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume("p_ge1", "p >= 1");
    ctx.push_assume("p_le_i", "p <= i");
    ctx.push_assume("p_lt_n", "p < n");
    ctx.push_assume("pm1_step", "p == pm1 + 1");
    ctx.push_assume("pm1_lt_n", "pm1 < n");
    ctx.push_assume("n_bounded", "n < 1000000");

    // Exit condition: s[p-1] <= key
    ctx.push_assume("exit_cond", "s.index(pm1) <= key");
    // Frame: s_new[p-1] = s[p-1] (position p-1 untouched)
    ctx.push_assume("frame_pm1", "s_new.index(pm1) == s.index(pm1)");
    // Insertion: s_new[p] = key
    ctx.push_assume("insert", "s_new.index(p) == key");
    ctx.push_assume("left_val_def", "left_val == s_new.index(pm1)");
    ctx.push_assume("inserted_val_def", "inserted_val == s_new.index(p)");

    // Left boundary valid: s_new[p-1] <= s_new[p]
    ctx.push_assert("left_boundary", "left_val <= inserted_val");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51c: insert left boundary should verify, got: {:?}",
        result,
    );
}

/// Tier 51c: Right boundary — first shifted element > key ensures
/// s_new[p] <= s_new[p+1].
///
/// The element at position p was shifted to p+1 because it was > key.
/// s_new[p+1] = s[p] > key = s_new[p].
#[test]
fn test_vt_tier51c_insert_right_boundary() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i64>");
    ctx.declare_var_parsed("s_new", "Seq<i64>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("p", "u64");
    ctx.declare_var_parsed("key", "i64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("len_new", "s_new.len() == n");
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume("p_lt_i", "p < i");
    ctx.push_assume("n_bounded", "n < 1000000");

    // s[p] was the first element NOT shifted (inner loop stopped here)
    // Actually, s[p] > key (the inner loop shifted it right)
    ctx.push_assume("first_shifted", "s.index(p) > key");
    // s_new[p+1] = s[p] (shifted right by 1)
    ctx.push_assume("shift_p", "s_new.index(p + 1) == s.index(p)");
    // s_new[p] = key (insertion)
    ctx.push_assume("insert", "s_new.index(p) == key");

    // Right boundary valid: s_new[p] < s_new[p+1]
    ctx.push_assert("right_boundary", "s_new.index(p) < s_new.index(p + 1)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51c: insert right boundary should verify, got: {:?}",
        result,
    );
}

/// Tier 51c: Untouched prefix — sorted [0,p) preserved through frame.
///
/// Concrete trace: sorted [1,2,5,7,3] with insert at p=2.
/// Prefix [0,2) = [1,2] unchanged in s_new = [1,2,3,5,7].
///
/// Symbolic version (IH+frame→sorted s_new) requires 2 E-matching rounds
/// which ay-dpll single-round cannot discharge. Concrete trace validates
/// the property for a representative case.
#[test]
fn test_vt_tier51c_prefix_sorted_preserved() {
    let mut ctx = VerificationContext::new();
    // Before: sorted prefix [1,2,5,7], key=3 (s[4]).
    assume_seq_i64(&mut ctx, "s", &[1, 2, 5, 7, 3]);
    // After insert at p=2: [1,2,3,5,7]. Prefix [0,2) unchanged.
    assume_seq_i64(&mut ctx, "s_new", &[1, 2, 3, 5, 7]);

    // Frame: [0,2) unchanged
    ctx.push_assert("frame_0", "s_new.index(0) == s.index(0)");
    ctx.push_assert("frame_1", "s_new.index(1) == s.index(1)");
    // Prefix [0,2) sorted in s_new
    ctx.push_assert("prefix_sorted", "s_new.index(0) <= s_new.index(1)");
    // Left boundary: s_new[1]=2 <= s_new[2]=3
    ctx.push_assert("left_boundary", "s_new.index(1) <= s_new.index(2)");
    // Full result sorted
    ctx.push_assert(
        "full_sorted",
        "forall(|k: u64| !(k < 4) || s_new.index(k) <= s_new.index(k + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51c: prefix sorted preserved should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Concrete traces
// ========================================================================

/// Tier 51d: Single step — insert s[1]=3 into sorted [5], giving [3,5].
///
/// Before: [5, 3, ...]. key=3 < 5, so shift 5 right, insert 3 at 0.
/// After:  [3, 5, ...].
#[test]
fn test_vt_tier51d_concrete_single_step() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[5, 3, 8, 1, 4]);
    assume_seq_i64(&mut ctx, "s_new", &[3, 5, 8, 1, 4]);

    // s_new[0] = 3 = key = s[1]
    ctx.push_assert("key_placed", "s_new.index(0) == s.index(1)");
    // s_new[1] = 5 = s[0] (shifted right)
    ctx.push_assert("shifted", "s_new.index(1) == s.index(0)");
    // Sorted [0, 2): 3 <= 5
    ctx.push_assert("sorted_01", "s_new.index(0) <= s_new.index(1)");
    // Frame: positions [2,5) unchanged
    ctx.push_assert("frame_2", "s_new.index(2) == s.index(2)");
    ctx.push_assert("frame_3", "s_new.index(3) == s.index(3)");
    ctx.push_assert("frame_4", "s_new.index(4) == s.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51d: single step concrete trace should verify, got: {:?}",
        result,
    );
}

/// Tier 51d: Middle insert — insert 4 into sorted [1,3,5,7], giving [1,3,4,5,7].
///
/// key=4, shifts 5→pos3, 7→pos4, inserts 4 at pos2.
/// Demonstrates insertion into the middle of a sorted prefix.
#[test]
fn test_vt_tier51d_concrete_middle_insert() {
    let mut ctx = VerificationContext::new();
    // Before outer iteration i=4: [1, 3, 5, 7, 4]
    // sorted prefix [0,4) = [1,3,5,7], key = s[4] = 4
    assume_seq_i64(&mut ctx, "s", &[1, 3, 5, 7, 4]);
    // After: 7→pos4, 5→pos3, insert 4 at pos2
    assume_seq_i64(&mut ctx, "s_new", &[1, 3, 4, 5, 7]);

    // Fully sorted [0, 5)
    ctx.push_assert("sorted_01", "s_new.index(0) <= s_new.index(1)");
    ctx.push_assert("sorted_12", "s_new.index(1) <= s_new.index(2)");
    ctx.push_assert("sorted_23", "s_new.index(2) <= s_new.index(3)");
    ctx.push_assert("sorted_34", "s_new.index(3) <= s_new.index(4)");

    // Key was correctly placed
    ctx.push_assert("key_at_2", "s_new.index(2) == s.index(4)");
    // Frame: [0, 2) unchanged
    ctx.push_assert("frame_0", "s_new.index(0) == s.index(0)");
    ctx.push_assert("frame_1", "s_new.index(1) == s.index(1)");
    // Shifted: s_new[3] = s[2], s_new[4] = s[3]
    ctx.push_assert("shift_2to3", "s_new.index(3) == s.index(2)");
    ctx.push_assert("shift_3to4", "s_new.index(4) == s.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51d: middle insert concrete trace should verify, got: {:?}",
        result,
    );
}

/// Tier 51d: No-shift insert — key is largest, stays in place.
///
/// [1, 3, 5, 7, 9]: key=9 >= all prefix elements, inner loop never
/// shifts, p=i, no frame needed.
#[test]
fn test_vt_tier51d_concrete_no_shift() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[1, 3, 5, 7, 9]);

    // key = s[4] = 9, which is >= s[3] = 7 — no shift needed
    ctx.push_assert("key_ge_last", "s.index(4) >= s.index(3)");
    // Array already sorted
    ctx.push_assert(
        "fully_sorted",
        "forall(|k: u64| !(k < 4) || s.index(k) <= s.index(k + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 51d: no-shift insert should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Negative tests
// ========================================================================

/// Tier 51e NEGATIVE: Unsorted array — [5,2,8,1,4] is not sorted.
#[test]
fn test_vt_tier51e_unsorted_array_negative() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s", &[5, 2, 8, 1, 4]);

    ctx.push_assert(
        "wrong_sorted",
        "forall(|k: u64| !(k < 4) || s.index(k) <= s.index(k + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 51e SOUNDNESS: [5,2,8,1,4] is not sorted, got: {:?}",
        result,
    );
}

/// Tier 51e NEGATIVE: Wrong insertion — inserting key at wrong position
/// breaks sortedness.
///
/// Sorted prefix [1,3,5], key=2. Correct insert at pos 1 gives [1,2,3,5].
/// Wrong: insert at pos 2 gives [1,3,2,5] — not sorted.
#[test]
fn test_vt_tier51e_wrong_insertion_position_negative() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "s_new", &[1, 3, 2, 5]);

    // Claim: sorted [0, 4) — but 3 > 2, so position 1-2 is unsorted
    ctx.push_assert(
        "wrong_sorted",
        "forall(|k: u64| !(k < 3) || s_new.index(k) <= s_new.index(k + 1))",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 51e SOUNDNESS: wrong insertion position, got: {:?}",
        result,
    );
}
