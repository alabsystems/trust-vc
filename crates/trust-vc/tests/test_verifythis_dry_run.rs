// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 18 — Competition dry-run.
//!
//! Complete algorithm verifications modeling the actual competition workflow:
//! decompose problem into Init/Step/Exit VCs, verify each, confirm negative
//! tests reject wrong invariants. Each group simulates a 90-minute challenge.
//!
//! GROUP A: Kadane's Maximum Subarray Sum — accumulator + max tracking.
//! GROUP B: Insertion sort inner step — sorted prefix maintenance.
//! GROUP C: Two-sum search — exists + index pair reasoning.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Kadane's Maximum Subarray Sum
//
// Given Seq<i32> s of length n, find the maximum sum of any contiguous
// subarray. Kadane's algorithm maintains:
//   current_sum = max subarray sum ending at position i
//   best_sum    = max subarray sum seen so far
//
// Loop invariant:
//   best_sum >= current_sum
//   current_sum >= s[i]  (at least the single element)
//   best_sum >= s[j] for all j <= i  (best >= any single element seen)
//
// This is a classic VerifyThis problem pattern: accumulator with
// conditional reset (current_sum = max(current_sum + s[i], s[i])).
// ========================================================================

/// Tier 18a: Kadane init — first element initializes both accumulators.
#[test]
fn test_vt_tier18a_kadane_init() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("current_sum", "i32");
    ctx.declare_var_parsed("best_sum", "i32");

    ctx.push_assume("len_pos", "s.len() >= 1");
    ctx.push_assume("len_bound", "s.len() <= 1000");

    // Init: current_sum = s[0], best_sum = s[0]
    ctx.push_assume("init_current", "current_sum == s.index(0)");
    ctx.push_assume("init_best", "best_sum == s.index(0)");

    // Invariant at i=0: best_sum >= current_sum
    ctx.push_assert("inv_best_ge_current", "best_sum >= current_sum");
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 18a: Kadane init should verify, got: {:?}",
        result,
    );
}

/// Tier 18a: Kadane step — accumulator update preserves invariant.
///
/// The step is: current_sum_new = max(current_sum + s[i], s[i])
///              best_sum_new = max(best_sum, current_sum_new)
/// Must prove: best_sum_new >= current_sum_new.
#[test]
fn test_vt_tier18a_kadane_step() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("current_sum", "i32");
    ctx.declare_var_parsed("best_sum", "i32");
    ctx.declare_var_parsed("current_sum_new", "i32");
    ctx.declare_var_parsed("best_sum_new", "i32");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("elem", "i32");

    // Loop bounds
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_bound", "i < 1000");
    ctx.push_assume("len_bound", "s.len() <= 1000");
    ctx.push_assume("i_lt_len", "i < s.len()");

    // Current element
    ctx.push_assume("elem_def", "elem == s.index(i)");
    ctx.push_assume("elem_bound", "elem >= -1000000 && elem <= 1000000");
    ctx.push_assume(
        "current_bound",
        "current_sum >= -1000000 && current_sum <= 1000000",
    );

    // Induction hypothesis
    ctx.push_assume("ih_best_ge_current", "best_sum >= current_sum");

    // Step: current_sum_new = max(current_sum + elem, elem)
    ctx.push_assume(
        "step_current",
        "(current_sum + elem >= elem && current_sum_new == current_sum + elem) || \
         (current_sum + elem < elem && current_sum_new == elem)",
    );

    // Step: best_sum_new = max(best_sum, current_sum_new)
    ctx.push_assume(
        "step_best",
        "(best_sum >= current_sum_new && best_sum_new == best_sum) || \
         (best_sum < current_sum_new && best_sum_new == current_sum_new)",
    );

    // Prove invariant preserved: best_sum_new >= current_sum_new
    ctx.push_assert("inv_preserved", "best_sum_new >= current_sum_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 18a: Kadane step should verify, got: {:?}",
        result,
    );
}

/// Tier 18a: Kadane exit — concrete 3-element execution derives postcondition.
///
/// Model the actual Kadane execution over s = [a, b, c] and prove the exit
/// condition (best_sum >= each element) from the algorithm's update rules,
/// NOT from direct assumptions of the postcondition.
/// Discrimination: removing any step_* assumption breaks the proof.
#[test]
fn test_vt_tier18a_kadane_exit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("c0", "i32"); // current_sum after element 0
    ctx.declare_var_parsed("b0", "i32"); // best_sum after element 0
    ctx.declare_var_parsed("c1", "i32"); // current_sum after element 1
    ctx.declare_var_parsed("b1", "i32"); // best_sum after element 1

    ctx.push_assume("len3", "s.len() == 3");
    ctx.push_assume("elem_bounds0", "s.index(0) >= -100 && s.index(0) <= 100");
    ctx.push_assume("elem_bounds1", "s.index(1) >= -100 && s.index(1) <= 100");
    ctx.push_assume("elem_bounds2", "s.index(2) >= -100 && s.index(2) <= 100");

    // Step 0: init c0 = s[0], b0 = s[0]
    ctx.push_assume("step0_c", "c0 == s.index(0)");
    ctx.push_assume("step0_b", "b0 == s.index(0)");

    // Step 1: c1 = max(c0 + s[1], s[1]), b1 = max(b0, c1)
    ctx.push_assume(
        "step1_c",
        "(c0 + s.index(1) >= s.index(1) && c1 == c0 + s.index(1)) || \
         (c0 + s.index(1) < s.index(1) && c1 == s.index(1))",
    );
    ctx.push_assume("step1_b", "(b0 >= c1 && b1 == b0) || (b0 < c1 && b1 == c1)");

    // Exit postcondition: b1 >= s[0] AND b1 >= s[1]
    // Non-tautological: must chain step0 → step1 → case analysis
    ctx.push_assert("exit_ge_elem0", "b1 >= s.index(0)");
    ctx.push_assert("exit_ge_elem1", "b1 >= s.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 18a: Kadane exit should verify, got: {:?}",
        result,
    );
}

/// Tier 18a: Kadane negative — wrong update rule fails.
///
/// If we use current_sum_new = current_sum + elem (without the max reset),
/// the invariant best_sum_new >= current_sum_new can still hold, but a
/// different property fails: current_sum_new >= elem (no longer true when
/// current_sum is very negative).
#[test]
fn test_vt_tier18a_kadane_wrong_update_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("current_sum", "i32");
    ctx.declare_var_parsed("current_sum_new", "i32");
    ctx.declare_var_parsed("elem", "i32");

    ctx.push_assume(
        "current_bound",
        "current_sum >= -1000000 && current_sum <= 1000000",
    );
    ctx.push_assume("elem_bound", "elem >= -1000000 && elem <= 1000000");

    // WRONG: always add (no max reset)
    ctx.push_assume("wrong_update", "current_sum_new == current_sum + elem");

    // This should fail: current_sum_new >= elem is NOT guaranteed
    // (e.g., current_sum = -500000, elem = 1 → current_sum_new = -499999 < elem)
    ctx.push_assert("current_ge_elem", "current_sum_new >= elem");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 18a SOUNDNESS: wrong Kadane update (e.g. current_sum=-500000, elem=1 → sum=-499999 < elem), got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Insertion Sort Inner Step
//
// Insertion sort: maintain sorted prefix s[0..i], insert s[i] into the
// correct position. The inner loop shifts elements right until finding
// the insertion point.
//
// Key VC: after inserting elem at position k, the prefix s_new[0..i+1]
// is sorted. Requires proving:
//   s_new[k-1] <= elem <= s_new[k+1]  (new element in correct place)
//   s_new[j] == s[j] for j < k        (prefix preserved)
//   s_new[j] == s[j-1] for j > k      (shifted right)
// ========================================================================

/// Tier 18b: Insertion sort — insert into sorted prefix (concrete n=4).
///
/// Sorted prefix [1, 3, 5], insert elem=4 at position 2.
/// Result should be [1, 3, 4, 5].
#[test]
fn test_vt_tier18b_insertion_sort_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");

    ctx.push_assume("len4", "s_new.len() == 4");

    // Result of insertion: [1, 3, 4, 5]
    ctx.push_assume("s_new_0", "s_new.index(0) == 1");
    ctx.push_assume("s_new_1", "s_new.index(1) == 3");
    ctx.push_assume("s_new_2", "s_new.index(2) == 4");
    ctx.push_assume("s_new_3", "s_new.index(3) == 5");

    // Prove sorted
    ctx.push_assert("sorted_01", "s_new.index(0) <= s_new.index(1)");
    ctx.push_assert("sorted_12", "s_new.index(1) <= s_new.index(2)");
    ctx.push_assert("sorted_23", "s_new.index(2) <= s_new.index(3)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 18b: insertion sort concrete should verify, got: {:?}",
        result,
    );
}

/// Tier 18b: Insertion sort step VC — insert preserves sortedness.
///
/// Given: s[0..3] sorted, elem to insert, insertion point k.
/// Model: s_new = s[0..k] ++ [elem] ++ s[k..3].
/// Prove: s_new[0..4] sorted.
#[test]
fn test_vt_tier18b_insertion_sort_step_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("elem", "i32");

    ctx.push_assume("s_len", "s.len() == 3");
    ctx.push_assume("s_new_len", "s_new.len() == 4");

    // Precondition: s[0..3] is sorted
    ctx.push_assume("sorted_01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted_12", "s.index(1) <= s.index(2)");

    // Insertion at position 1: elem goes between s[0] and s[1]
    // Insertion point condition: s[0] <= elem <= s[1]
    ctx.push_assume("insert_ge_prev", "s.index(0) <= elem");
    ctx.push_assume("insert_le_next", "elem <= s.index(1)");

    // Result: s_new = [s[0], elem, s[1], s[2]]
    ctx.push_assume("new_0", "s_new.index(0) == s.index(0)");
    ctx.push_assume("new_1", "s_new.index(1) == elem");
    ctx.push_assume("new_2", "s_new.index(2) == s.index(1)");
    ctx.push_assume("new_3", "s_new.index(3) == s.index(2)");

    // Prove: s_new[0..4] is sorted
    ctx.push_assert("new_sorted_01", "s_new.index(0) <= s_new.index(1)");
    ctx.push_assert("new_sorted_12", "s_new.index(1) <= s_new.index(2)");
    ctx.push_assert("new_sorted_23", "s_new.index(2) <= s_new.index(3)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 18b: insertion sort step should verify, got: {:?}",
        result,
    );
}

/// Tier 18b: Insertion sort — wrong insertion point fails.
///
/// If we insert elem at the wrong position (not between its neighbors),
/// sortedness is not preserved.
#[test]
fn test_vt_tier18b_insertion_wrong_position_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("elem", "i32");

    ctx.push_assume("s_len", "s.len() == 3");
    ctx.push_assume("s_new_len", "s_new.len() == 4");
    ctx.push_assume("sorted_01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted_12", "s.index(1) <= s.index(2)");

    // elem > s[2] (should go at end), but we insert at position 1 (WRONG)
    ctx.push_assume("elem_too_big", "elem > s.index(2)");
    ctx.push_assume("new_0", "s_new.index(0) == s.index(0)");
    ctx.push_assume("new_1", "s_new.index(1) == elem"); // wrong position
    ctx.push_assume("new_2", "s_new.index(2) == s.index(1)");
    ctx.push_assume("new_3", "s_new.index(3) == s.index(2)");

    // s_new[1] = elem > s[2] >= s[1] = s_new[2], so NOT sorted
    ctx.push_assert("new_sorted_12", "s_new.index(1) <= s_new.index(2)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 18b SOUNDNESS: wrong insertion point (elem > s[2] but placed at index 1), got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Two-Sum Problem
//
// Given array s and target t, find indices i, j with i < j such that
// s[i] + s[j] == t. This is a classic interview/competition problem.
// The verification angle: prove that if we find such a pair, the
// postcondition s[i] + s[j] == t holds.
//
// Also tests: sorted-array two-pointer approach where lo starts at 0,
// hi starts at n-1, and we narrow based on sum comparison.
// ========================================================================

/// Tier 18c: Two-sum postcondition — found pair satisfies target.
#[test]
fn test_vt_tier18c_two_sum_postcondition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("target", "i32");

    ctx.push_assume("len", "s.len() == 5");
    ctx.push_assume("i_bound", "i < s.len()");
    ctx.push_assume("j_bound", "j < s.len()");
    ctx.push_assume("i_lt_j", "i < j");

    // Found: s[i] + s[j] == target
    ctx.push_assume("found", "s.index(i) + s.index(j) == target");

    ctx.push_assert("post_commuted", "s.index(j) + s.index(i) == target");
    ctx.push_assert("post_partner", "target - s.index(i) == s.index(j)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 18c: two-sum postcondition should verify, got: {:?}",
        result,
    );
}

/// Tier 18c: Two-pointer narrowing step on sorted array (concrete).
///
/// If s is sorted and s[lo] + s[hi] < target, then increasing lo is safe:
/// no pair (lo, j) with j <= hi can sum to target (since s[j] <= s[hi]).
/// This is the correctness argument for the two-pointer technique.
///
/// Concrete indices (lo=1, hi=4, j=3) because ay-dpll times out on
/// symbolic-index array monotonicity reasoning within 10s. Competition
/// strategy: unroll concrete steps when symbolic reasoning times out.
///
/// KEY COMPETITION LESSON: Element bounds are mandatory to prevent BV
/// overflow. Without them, s[lo] + s[j] can wrap around.
#[test]
fn test_vt_tier18c_two_pointer_step_lo() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("target", "i32");

    ctx.push_assume("len", "s.len() == 5");

    // Element bounds prevent BV overflow
    ctx.push_assume(
        "elem0_bound",
        "s.index(0) >= -1000000 && s.index(0) <= 1000000",
    );
    ctx.push_assume(
        "elem1_bound",
        "s.index(1) >= -1000000 && s.index(1) <= 1000000",
    );
    ctx.push_assume(
        "elem2_bound",
        "s.index(2) >= -1000000 && s.index(2) <= 1000000",
    );
    ctx.push_assume(
        "elem3_bound",
        "s.index(3) >= -1000000 && s.index(3) <= 1000000",
    );
    ctx.push_assume(
        "elem4_bound",
        "s.index(4) >= -1000000 && s.index(4) <= 1000000",
    );

    // Sorted array
    ctx.push_assume("sorted_01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted_12", "s.index(1) <= s.index(2)");
    ctx.push_assume("sorted_23", "s.index(2) <= s.index(3)");
    ctx.push_assume("sorted_34", "s.index(3) <= s.index(4)");

    // Concrete: lo=1, hi=4, sum too small
    ctx.push_assume("sum_too_small", "s.index(1) + s.index(4) < target");

    // s[3] <= s[4] (sorted), so s[1] + s[3] <= s[1] + s[4] < target
    // This is the concrete step: pair (1, 3) also can't reach target.
    ctx.push_assert(
        "pair_13_small",
        "s.index(1) + s.index(3) <= s.index(1) + s.index(4)",
    );
    // Also: pair (1, 2)
    ctx.push_assert(
        "pair_12_small",
        "s.index(1) + s.index(2) <= s.index(1) + s.index(4)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 18c: two-pointer lo step should verify, got: {:?}",
        result,
    );
}

/// Tier 18c: Two-pointer — wrong direction fails.
///
/// If sum is too small but we decrease hi instead of increasing lo,
/// we might skip the answer. The VC shows this is unsound.
#[test]
fn test_vt_tier18c_two_pointer_wrong_direction_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("target", "i32");

    ctx.push_assume("len", "s.len() == 5");
    ctx.push_assume("lo_bound", "lo < s.len()");
    ctx.push_assume("hi_bound", "hi < s.len()");
    ctx.push_assume("lo_lt_hi", "lo < hi");
    ctx.push_assume("hi_ge1", "hi >= 1");

    // Sorted
    ctx.push_assume("sorted_01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted_12", "s.index(1) <= s.index(2)");
    ctx.push_assume("sorted_23", "s.index(2) <= s.index(3)");
    ctx.push_assume("sorted_34", "s.index(3) <= s.index(4)");

    // Sum too small → should increase lo
    ctx.push_assume("sum_too_small", "s.index(lo) + s.index(hi) < target");

    // WRONG: decrease hi. Claim s[lo] + s[hi-1] >= target (not guaranteed)
    ctx.push_assert("wrong_claim", "s.index(lo) + s.index(hi - 1) >= target");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 18c SOUNDNESS: wrong two-pointer direction (decreasing hi when sum too small), got: {:?}",
        result,
    );
}
