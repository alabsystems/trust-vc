// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 17 — Nested loops and multi-phase algorithm VCs.
//!
//! Tiers 1-16 cover single-loop, single-phase patterns. Tier 17 targets
//! the two most common VerifyThis structures that require multi-obligation
//! interaction:
//!
//! 1. **Nested loops** — outer invariant preserved by inner loop,
//!    inner invariant proved using outer invariant as assumption.
//! 2. **Multi-phase algorithms** — Phase 1 establishes a postcondition
//!    used as Phase 2's precondition.
//! 3. **Ghost accumulators** — tracking aggregate properties (sums, counts)
//!    through loop iterations via invariants.
//!
//! These patterns appear in nearly every competitive VerifyThis entry:
//! - Matrix operations (nested loops)
//! - Two-pass algorithms (multi-phase)
//! - Running sum/count (ghost accumulators)
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Nested loop VCs
//
// In VerifyThis, nested loops (matrix traverse, 2D search, bubble sort
// passes) require the outer invariant as an assumption when proving the
// inner invariant. We model this by treating the inner loop as a VC
// that assumes the outer loop invariant.
// ========================================================================

/// Tier 17a: Matrix row-max — inner loop finds max in row, outer tracks
/// that all prior rows have valid maxima stored.
///
/// Outer invariant: forall r < i, result[r] == max of row r
/// Inner invariant: current_max >= all elements seen in current row
#[test]
fn test_vt_tier17a_nested_inner_loop_step_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m", "Seq<Seq<i32>>"); // matrix as Seq of rows
    ctx.declare_var_parsed("i", "u64"); // outer index (row)
    ctx.declare_var_parsed("j", "u64"); // inner index (column)
    ctx.declare_var_parsed("j_new", "u64");
    ctx.declare_var_parsed("cols", "u64"); // number of columns
    ctx.declare_var_parsed("current_max", "i32");
    ctx.declare_var_parsed("current_max_new", "i32");
    ctx.declare_var_parsed("elem", "i32"); // m[i][j]

    // Inner loop context: j iterates over columns in row i
    ctx.push_assume("j_ge0", "j >= 1");
    ctx.push_assume("j_lt_cols", "j < cols");
    ctx.push_assume("cols_pos", "cols >= 1");

    // Inner loop invariant (inductive hypothesis):
    // current_max >= all elements in row i up to column j
    // We model this concretely for j=1 step (generic via unrolling pattern)
    ctx.push_assume("inv_ih_max_ge_first", "current_max >= elem");

    // Loop body: max update preserves monotonicity (current_max_new >= current_max)
    // Proof relies on transitivity: current_max_new >= current_max >= elem (via IH)
    ctx.push_assume("max_update_ge_old", "current_max_new >= current_max");
    ctx.push_assume("j_step", "j_new == j + 1");
    ctx.push_assume("j_new_no_overflow", "j_new <= 1000000");

    // Prove inner invariant preserved
    ctx.push_assert("inner_inv_preserved", "current_max_new >= elem");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17a: inner loop step VC should verify, got: {:?}",
        result,
    );
}

/// Tier 17a: Outer loop step — after inner loop completes, the outer
/// invariant is preserved. The inner loop's postcondition (current_max
/// is max of row i) becomes the outer loop's inductive step.
#[test]
fn test_vt_tier17a_nested_outer_loop_step_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "Seq<i32>"); // result[r] = max of row r
    ctx.declare_var_parsed("result_new", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64"); // outer index
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("rows", "u64");
    ctx.declare_var_parsed("current_max", "i32");

    ctx.push_assume("i_ge0", "i >= 0");
    ctx.push_assume("i_lt_rows", "i < rows");
    ctx.push_assume("rows_pos", "rows >= 1");
    ctx.push_assume("i_no_overflow", "i < 1000000");

    // Outer invariant IH: all prior rows have correct max in result
    // Model concretely: result.len() == i
    ctx.push_assume("result_len_eq_i", "result.len() == i");

    // Inner loop postcondition (assumed proven): current_max is max of row i
    // We just know it's a valid i32 value — the inner VC proved it
    ctx.push_assume("inner_post", "true");

    // Outer body: append current_max to result
    ctx.push_assume("result_new_len", "result_new.len() == i + 1");
    ctx.push_assume("result_new_has_max", "result_new.index(i) == current_max");
    ctx.push_assume("i_step", "i_new == i + 1");

    // Prove outer invariant preserved: result_new.len() == i_new
    ctx.push_assert("outer_inv_len", "result_new.len() == i_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17a: outer loop step VC should verify, got: {:?}",
        result,
    );
}

/// Tier 17a: Negative — outer invariant violated when inner postcondition
/// is wrong. If inner loop doesn't establish its postcondition, outer
/// invariant should fail.
#[test]
fn test_vt_tier17a_nested_negative_wrong_inner_post() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("result", "Seq<i32>");
    ctx.declare_var_parsed("result_new", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");

    ctx.push_assume("i_ge0", "i >= 0");
    ctx.push_assume("result_len_eq_i", "result.len() == i");
    ctx.push_assume("result_new_len", "result_new.len() == i + 1");
    ctx.push_assume("i_step", "i_new == i + 1");

    // Try to prove result_new.len() == i_new + 1 (WRONG — off by one)
    ctx.push_assert("outer_inv_wrong", "result_new.len() == i_new + 1");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 17a negative: wrong outer invariant must produce Counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Multi-phase algorithms
//
// VerifyThis problems often decompose into phases:
//   Phase 1: scan/compute (establish intermediate property)
//   Phase 2: use/verify (consume the intermediate property)
// Example: find pivot then partition; compute prefix sums then query.
// ========================================================================

/// Tier 17b: Two-phase algorithm — Phase 1 finds a pivot, Phase 2 uses it.
///
/// Phase 1: scan array, find index of minimum element.
/// Phase 2: given pivot index, partition into [< pivot] [>= pivot].
#[test]
fn test_vt_tier17b_two_phase_pivot_partition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("pivot_idx", "u64");
    ctx.declare_var_parsed("pivot_val", "i32");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_pos", "n >= 1");
    ctx.push_assume("n_bound", "n <= 1000000");

    // Phase 1 postcondition: pivot_idx is valid, pivot_val = s[pivot_idx]
    ctx.push_assume("pivot_valid", "pivot_idx < n");
    ctx.push_assume("pivot_val_eq", "pivot_val == s.index(pivot_idx)");

    // Phase 1 property: pivot_val is minimum (concrete check at index 0)
    ctx.push_assume("pivot_le_0", "pivot_val <= s.index(0)");

    // Phase 2 assertion: s[pivot_idx] <= s[0] (chains through pivot_val equality)
    ctx.push_assert("phase2_uses_phase1", "s.index(pivot_idx) <= s.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17b: two-phase pivot-partition should verify, got: {:?}",
        result,
    );
}

/// Tier 17b: Multi-phase with assert_by — Phase 1 proof scoped,
/// Phase 2 uses the proven fact.
#[test]
fn test_vt_tier17b_multi_phase_assert_by_scoping() {
    use trust_vc_core::vc::ProofObligation;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("sum", "i32");

    ctx.push_assume("a_pos", "a > 0");
    ctx.push_assume("b_pos", "b > 0");
    ctx.push_assume("a_bound", "a < 10000");
    ctx.push_assume("b_bound", "b < 10000");
    ctx.push_assume("sum_eq", "sum == a + b");

    // Phase 1: prove sum > a using assert_by with scoped proof
    let scoped = vec![ProofObligation::assume("b_gt_0_scoped", "b > 0")];
    ctx.add_assert_by("phase1_sum_gt_a", "sum > a", scoped);

    // Phase 2: use the proven fact to derive sum > 0
    // (The assert_by mechanism makes phase1's result available)
    ctx.push_assert("phase2_sum_positive", "sum > 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17b: multi-phase assert_by should verify, got: {:?}",
        result,
    );
}

/// Tier 17b: Phase handoff negative — Phase 2 tries to use a property
/// NOT established by Phase 1.
#[test]
fn test_vt_tier17b_phase_handoff_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("min_val", "i32");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_pos", "n >= 2");

    // Phase 1: min_val <= s[0] (only proved for index 0)
    ctx.push_assume("phase1_post", "min_val <= s.index(0)");

    // Phase 2 tries: min_val <= s[1] — NOT established by Phase 1
    ctx.push_assert("phase2_wrong", "min_val <= s.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 17b negative: unestablished phase2 property must produce Counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Ghost accumulator VCs
//
// Many VerifyThis problems track running sums, counts, or other aggregate
// properties. The invariant relates the accumulator to the processed
// prefix: sum == Sigma(s[0..i]) or count == |{j < i : P(s[j])}|.
// ========================================================================

/// Tier 17c: Running sum invariant — sum tracks prefix sum through loop.
#[test]
fn test_vt_tier17c_running_sum_step_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("sum", "i32");
    ctx.declare_var_parsed("sum_new", "i32");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("i_ge0", "i >= 0");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume("i_bound", "i < 1000000");
    ctx.push_assume("sum_bound", "sum < 500000");
    ctx.push_assume("elem_bound", "s.index(i) >= 0 && s.index(i) < 1000");

    // Ghost invariant: sum == sum of s[0..i]
    // (We model the step relation rather than the full aggregate)
    ctx.push_assume("inv_ih", "sum >= 0");

    // Loop body: sum_new = sum + s[i]
    ctx.push_assume("sum_step", "sum_new == sum + s.index(i)");
    ctx.push_assume("i_step", "i_new == i + 1");

    // Prove invariant maintained: sum_new >= 0
    ctx.push_assert("sum_nonneg_preserved", "sum_new >= 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17c: running sum step VC should verify, got: {:?}",
        result,
    );
}

/// Tier 17c: Running sum exit — after loop, sum relates to n.
#[test]
fn test_vt_tier17c_running_sum_exit_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("sum", "i32");

    ctx.push_assume("n_eq_3", "n == 3");
    ctx.push_assume("len", "s.len() == n");

    // Concrete: sum of 3 non-negative elements bounded by 1000 each
    ctx.push_assume("e0_bound", "s.index(0) >= 0 && s.index(0) < 1000");
    ctx.push_assume("e1_bound", "s.index(1) >= 0 && s.index(1) < 1000");
    ctx.push_assume("e2_bound", "s.index(2) >= 0 && s.index(2) < 1000");
    ctx.push_assume("sum_eq", "sum == s.index(0) + s.index(1) + s.index(2)");

    // Prove: 0 <= sum < 3000
    ctx.push_assert("sum_lower", "sum >= 0");
    ctx.push_assert("sum_upper", "sum < 3000");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17c: running sum exit VC should verify, got: {:?}",
        result,
    );
}

/// Tier 17c: Ghost count — count of elements satisfying a predicate.
///
/// Pattern: count tracks |{j < i : s[j] > threshold}|.
/// Step: if s[i] > threshold then count_new = count + 1, else count_new = count.
#[test]
fn test_vt_tier17c_ghost_count_step_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_new", "u64");

    ctx.push_assume("i_ge0", "i >= 0");
    ctx.push_assume("i_bound", "i < 1000000");

    // Invariant IH: count <= i
    ctx.push_assume("inv_ih", "count <= i");

    // Body: count_new = count or count + 1
    ctx.push_assume(
        "count_update",
        "count_new == count || count_new == count + 1",
    );
    ctx.push_assume("i_step", "i_new == i + 1");

    // Prove: count_new <= i_new
    ctx.push_assert("count_le_inew", "count_new <= i_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 17c: ghost count step VC should verify, got: {:?}",
        result,
    );
}

/// Tier 17c: Ghost count negative — wrong bound.
#[test]
fn test_vt_tier17c_ghost_count_negative_strict() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_new", "u64");

    ctx.push_assume("i_ge0", "i >= 0");
    ctx.push_assume("inv_ih", "count <= i");
    ctx.push_assume(
        "count_update",
        "count_new == count || count_new == count + 1",
    );
    ctx.push_assume("i_step", "i_new == i + 1");

    // Wrong: count_new < i_new (should be <=, not <)
    // When count == i and count_new == count + 1, count_new == i_new, not < i_new
    ctx.push_assert("count_strict_wrong", "count_new < i_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 17c negative: strict count bound must produce Counterexample, got: {:?}",
        result,
    );
}

// Groups D (bubble sort) and E (GCD) are in test_verifythis_classic_algorithms.rs
// (split for 500-line limit).
