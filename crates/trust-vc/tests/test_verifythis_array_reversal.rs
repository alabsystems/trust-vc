// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 56 — Array Reversal (Two-Pointer In-Place Swap) VCs.
//!
//! In-place array reversal is the canonical two-pointer pattern. Given
//! `a[0..n]`, we swap `a[lo]` with `a[hi]` while `lo < hi`, then advance
//! both pointers. This appears in VerifyThis problems involving rotation,
//! palindrome checks, and partition algorithms.
//!
//! Invariant at each step:
//!   - `a[0..lo]` holds the reversed suffix of the original
//!   - `a[hi+1..n]` holds the reversed prefix of the original
//!   - `a[lo..=hi]` is the untouched middle
//!   - `lo + hi == n - 1`  (pointers are symmetric)
//!
//! Core proof obligations:
//!   1. Init: lo=0, hi=n-1, array unchanged
//!   2. Step: swap preserves reversal invariant and pointer symmetry
//!   3. Exit: lo >= hi means the entire array is reversed
//!   4. Negatives: wrong swap or broken pointer motion rejected
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
// GROUP A: Init — entry conditions
// ========================================================================

/// Tier 56a: Init — lo=0, hi=n-1, array is the original.
/// For a = [10, 20, 30, 40], lo=0, hi=3.
#[test]
fn test_vt_tier56a_array_reversal_init() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[10, 20, 30, 40]);

    ctx.declare_var_parsed("lo", "i64");
    ctx.declare_var_parsed("hi", "i64");
    ctx.push_assume("lo_init", "lo == 0");
    ctx.push_assume("hi_init", "hi == 3");

    // Pointer symmetry
    ctx.push_assert("sym", "lo + hi == a.len() - 1");
    // lo < hi so we must iterate
    ctx.push_assert("need_work", "lo < hi");
    // Middle region is the whole array
    ctx.push_assert("mid_0", "a.index(0) == 10");
    ctx.push_assert("mid_3", "a.index(3) == 40");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56a: array reversal init should verify, got: {:?}",
        result,
    );
}

/// Tier 56a: Init — odd-length array: lo=0, hi=4 for n=5.
#[test]
fn test_vt_tier56a_array_reversal_init_odd() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[1, 2, 3, 4, 5]);

    ctx.declare_var_parsed("lo", "i64");
    ctx.declare_var_parsed("hi", "i64");
    ctx.push_assume("lo_init", "lo == 0");
    ctx.push_assume("hi_init", "hi == 4");

    ctx.push_assert("sym", "lo + hi == a.len() - 1");
    ctx.push_assert("need_work", "lo < hi");
    // Middle element (index 2) exists and stays unchanged at exit
    ctx.push_assert("center_exists", "a.index(2) == 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56a: odd-length array reversal init should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — swap preserves reversal invariant
// ========================================================================

/// Tier 56b: Step — first swap: a=[10,20,30,40] → a'=[40,20,30,10], lo'=1, hi'=2.
/// After swap(lo=0, hi=3): a'[0]=a[3], a'[3]=a[0], middle unchanged.
#[test]
fn test_vt_tier56b_first_swap_step() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[10, 20, 30, 40]);
    assume_seq_i64(&mut ctx, "a_new", &[40, 20, 30, 10]);

    ctx.declare_var_parsed("lo", "i64");
    ctx.declare_var_parsed("hi", "i64");
    ctx.declare_var_parsed("lo_new", "i64");
    ctx.declare_var_parsed("hi_new", "i64");
    ctx.push_assume("lo_val", "lo == 0");
    ctx.push_assume("hi_val", "hi == 3");
    ctx.push_assume("lo_new_val", "lo_new == 1");
    ctx.push_assume("hi_new_val", "hi_new == 2");

    // Swap correctness: a'[lo] = a[hi], a'[hi] = a[lo]
    ctx.push_assert("swap_lo", "a_new.index(0) == a.index(3)");
    ctx.push_assert("swap_hi", "a_new.index(3) == a.index(0)");
    // Middle unchanged
    ctx.push_assert("mid_1", "a_new.index(1) == a.index(1)");
    ctx.push_assert("mid_2", "a_new.index(2) == a.index(2)");
    // Pointer advance
    ctx.push_assert("lo_inc", "lo_new == lo + 1");
    ctx.push_assert("hi_dec", "hi_new == hi - 1");
    // Symmetry preserved
    ctx.push_assert("sym_new", "lo_new + hi_new == a.len() - 1");
    // Still need more work
    ctx.push_assert("continue", "lo_new < hi_new");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56b: first swap step should verify, got: {:?}",
        result,
    );
}

/// Tier 56b: Step — second swap: a'=[40,20,30,10] → a''=[40,30,20,10], lo'=2, hi'=1.
/// After swap(lo=1, hi=2): lo >= hi, so we stop.
#[test]
fn test_vt_tier56b_second_swap_step_exit() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a_pre", &[40, 20, 30, 10]);
    assume_seq_i64(&mut ctx, "a_post", &[40, 30, 20, 10]);

    ctx.declare_var_parsed("lo", "i64");
    ctx.declare_var_parsed("hi", "i64");
    ctx.declare_var_parsed("lo_new", "i64");
    ctx.declare_var_parsed("hi_new", "i64");
    ctx.push_assume("lo_val", "lo == 1");
    ctx.push_assume("hi_val", "hi == 2");
    ctx.push_assume("lo_new_val", "lo_new == 2");
    ctx.push_assume("hi_new_val", "hi_new == 1");

    // Swap correctness
    ctx.push_assert("swap_lo", "a_post.index(1) == a_pre.index(2)");
    ctx.push_assert("swap_hi", "a_post.index(2) == a_pre.index(1)");
    // Endpoints unchanged
    ctx.push_assert("keep_0", "a_post.index(0) == a_pre.index(0)");
    ctx.push_assert("keep_3", "a_post.index(3) == a_pre.index(3)");
    // Exit condition: lo >= hi
    ctx.push_assert("done", "lo_new >= hi_new");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56b: second swap + exit should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Exit — full reversal correctness
// ========================================================================

/// Tier 56c: Exit — after both swaps, array is fully reversed.
/// Original [10, 20, 30, 40] → [40, 30, 20, 10].
#[test]
fn test_vt_tier56c_full_reversal_correctness() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40]);
    assume_seq_i64(&mut ctx, "rev", &[40, 30, 20, 10]);

    // rev[i] == orig[n-1-i] for all i
    ctx.push_assert("rev_0", "rev.index(0) == orig.index(3)");
    ctx.push_assert("rev_1", "rev.index(1) == orig.index(2)");
    ctx.push_assert("rev_2", "rev.index(2) == orig.index(1)");
    ctx.push_assert("rev_3", "rev.index(3) == orig.index(0)");
    // Length preserved
    ctx.push_assert("len_eq", "rev.len() == orig.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56c: full reversal correctness should verify, got: {:?}",
        result,
    );
}

/// Tier 56c: Exit — odd-length reversal: [1,2,3,4,5] → [5,4,3,2,1].
/// The center element (3) is a fixed point of reversal when n is odd.
#[test]
fn test_vt_tier56c_odd_length_reversal() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "orig", &[1, 2, 3, 4, 5]);
    assume_seq_i64(&mut ctx, "rev", &[5, 4, 3, 2, 1]);

    ctx.push_assert("rev_0", "rev.index(0) == orig.index(4)");
    ctx.push_assert("rev_1", "rev.index(1) == orig.index(3)");
    ctx.push_assert("center_fixed", "rev.index(2) == orig.index(2)");
    ctx.push_assert("rev_3", "rev.index(3) == orig.index(1)");
    ctx.push_assert("rev_4", "rev.index(4) == orig.index(0)");
    ctx.push_assert("len_eq", "rev.len() == orig.len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56c: odd-length reversal should verify, got: {:?}",
        result,
    );
}

/// Tier 56c: Exit — double reversal is identity: rev(rev(a)) == a.
#[test]
fn test_vt_tier56c_double_reversal_identity() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40]);
    assume_seq_i64(&mut ctx, "rev1", &[40, 30, 20, 10]);
    assume_seq_i64(&mut ctx, "rev2", &[10, 20, 30, 40]);

    // rev1 is reverse of orig
    ctx.push_assert("r1_0", "rev1.index(0) == orig.index(3)");
    ctx.push_assert("r1_3", "rev1.index(3) == orig.index(0)");
    // rev2 is reverse of rev1
    ctx.push_assert("r2_0", "rev2.index(0) == rev1.index(3)");
    ctx.push_assert("r2_3", "rev2.index(3) == rev1.index(0)");
    // rev2 == orig
    ctx.push_assert("id_0", "rev2.index(0) == orig.index(0)");
    ctx.push_assert("id_1", "rev2.index(1) == orig.index(1)");
    ctx.push_assert("id_2", "rev2.index(2) == orig.index(2)");
    ctx.push_assert("id_3", "rev2.index(3) == orig.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56c: double reversal identity should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Symbolic step — pointer invariant
// ========================================================================

/// Tier 56d: Symbolic — pointer symmetry lo + hi == n - 1 is preserved
/// across an arbitrary swap step.
#[test]
fn test_vt_tier56d_pointer_symmetry_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("lo", "int");
    ctx.declare_var_parsed("hi", "int");
    ctx.declare_var_parsed("lo_new", "int");
    ctx.declare_var_parsed("hi_new", "int");
    ctx.declare_var_parsed("n", "int");

    ctx.push_assume("n_pos", "n >= 2");
    ctx.push_assume("lo_ge_0", "lo >= 0");
    ctx.push_assume("hi_lt_n", "hi < n");
    ctx.push_assume("lo_lt_hi", "lo < hi");
    // IH: symmetry holds before step
    ctx.push_assume("ih_sym", "lo + hi == n - 1");
    // Step: advance pointers
    ctx.push_assume("step_lo", "lo_new == lo + 1");
    ctx.push_assume("step_hi", "hi_new == hi - 1");

    // Symmetry preserved
    ctx.push_assert("sym_preserved", "lo_new + hi_new == n - 1");
    // Pointers move toward each other
    ctx.push_assert("converge", "hi_new - lo_new < hi - lo");
    // Both stay in bounds
    ctx.push_assert("lo_new_ge_0", "lo_new >= 0");
    ctx.push_assert("hi_new_lt_n", "hi_new < n");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56d: pointer symmetry preservation should verify, got: {:?}",
        result,
    );
}

/// Tier 56d: Symbolic — termination: distance hi-lo decreases by 2 each step.
#[test]
fn test_vt_tier56d_termination_distance_decreases() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("lo", "int");
    ctx.declare_var_parsed("hi", "int");
    ctx.declare_var_parsed("lo_new", "int");
    ctx.declare_var_parsed("hi_new", "int");

    ctx.push_assume("lo_ge_0", "lo >= 0");
    ctx.push_assume("lo_lt_hi", "lo < hi");
    ctx.push_assume("step_lo", "lo_new == lo + 1");
    ctx.push_assume("step_hi", "hi_new == hi - 1");

    // Distance decreases by exactly 2
    ctx.push_assert("distance_dec", "hi_new - lo_new == (hi - lo) - 2");
    // Old distance was positive, so it's either still positive or <= 0 (done)
    ctx.push_assert("progress", "hi_new - lo_new < hi - lo");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 56d: termination distance decrease should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Soundness negatives
// ========================================================================

/// Tier 56e NEGATIVE: Swapping the same element (lo == hi) changes nothing
/// but claiming a[lo] changed should fail.
#[test]
fn test_vt_tier56e_noop_swap_same_index_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "a", &[10, 20, 30]);

    // lo == hi == 1, "swap" does nothing
    ctx.declare_var_parsed("lo", "i64");
    ctx.push_assume("lo_val", "lo == 1");
    // Claiming a[1] changed after noop swap should fail
    ctx.push_assert("wrong_change", "a.index(1) != 20");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 56e SOUNDNESS: noop swap should reject change claim, got: {:?}",
        result,
    );
}

/// Tier 56e NEGATIVE: Wrong swap direction — swapping a[lo] with a[lo+1]
/// instead of a[hi] produces the wrong reversal.
#[test]
fn test_vt_tier56e_wrong_swap_partner_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "orig", &[10, 20, 30, 40]);
    // Wrong: swap(0, 1) instead of swap(0, 3) → [20, 10, 30, 40]
    assume_seq_i64(&mut ctx, "wrong", &[20, 10, 30, 40]);

    // Claiming wrong[0] == orig[3] should fail (wrong[0]=20, orig[3]=40)
    ctx.push_assert("wrong_swap", "wrong.index(0) == orig.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 56e SOUNDNESS: wrong swap partner should be rejected, got: {:?}",
        result,
    );
}

/// Tier 56e NEGATIVE: Claiming reversal produces a sorted array for
/// an unsorted input should fail.
#[test]
fn test_vt_tier56e_reversal_not_sorted_rejected() {
    let mut ctx = VerificationContext::new();
    // orig = [3, 1, 4, 2], rev = [2, 4, 1, 3] — not sorted
    assume_seq_i64(&mut ctx, "rev", &[2, 4, 1, 3]);

    // Claiming the reversal is sorted (ascending)
    ctx.push_assert(
        "sorted",
        "rev.index(0) <= rev.index(1) && rev.index(1) <= rev.index(2) && rev.index(2) <= rev.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 56e SOUNDNESS: unsorted reversal should reject sorted claim, got: {:?}",
        result,
    );
}
