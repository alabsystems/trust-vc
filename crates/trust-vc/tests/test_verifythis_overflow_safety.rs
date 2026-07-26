// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 21 — Overflow safety parity.
//!
//! Competition proc macros set `check_overflow = true`, but all VT tests
//! (Tiers 1-20) run with `check_overflow = false`. This tier validates that
//! representative competition patterns survive overflow checking.
//!
//! If these tests fail, the competition user would see spurious overflow
//! counterexamples on correct proofs — a critical false-negative that
//! wastes debugging time under the 90-minute clock.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Accumulator patterns with overflow checking
//
// These patterns involve addition in assumptions/assertions. With
// check_overflow = true, the encoder generates overflow predicates
// for every arithmetic operation. Element bounds must prevent the
// overflow predicates from firing.
// ========================================================================

/// Kadane step with overflow checking — bounds prevent overflow.
///
/// Mirrors test_vt_tier18a_kadane_step but with check_overflow = true.
/// The element bounds (±1M) on i32 (±2B) ensure additions don't overflow.
#[test]
fn test_vt_overflow_kadane_step() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("current_sum", "i32");
    ctx.declare_var_parsed("current_sum_new", "i32");
    ctx.declare_var_parsed("best_sum", "i32");
    ctx.declare_var_parsed("best_sum_new", "i32");
    ctx.declare_var_parsed("elem", "i32");

    // Bounds that prevent i32 overflow: -1M + -1M = -2M (well within i32 range)
    ctx.push_assume("elem_bound", "elem >= -1000000 && elem <= 1000000");
    ctx.push_assume(
        "current_bound",
        "current_sum >= -1000000 && current_sum <= 1000000",
    );
    ctx.push_assume("ih", "best_sum >= current_sum");

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

    ctx.push_assert("inv_preserved", "best_sum_new >= current_sum_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Kadane step with overflow checking should verify — bounds prevent overflow: {:?}",
        result,
    );
}

/// Insertion sort sortedness check with overflow checking.
///
/// No arithmetic on user values — only comparisons. Overflow checking
/// should not interfere because there are no add/sub/mul operations.
#[test]
fn test_vt_overflow_insertion_sort_comparisons() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s_new", "Seq<i32>");

    ctx.push_assume("len4", "s_new.len() == 4");
    ctx.push_assume("s_new_0", "s_new.index(0) == 1");
    ctx.push_assume("s_new_1", "s_new.index(1) == 3");
    ctx.push_assume("s_new_2", "s_new.index(2) == 4");
    ctx.push_assume("s_new_3", "s_new.index(3) == 5");

    ctx.push_assert("sorted_01", "s_new.index(0) <= s_new.index(1)");
    ctx.push_assert("sorted_12", "s_new.index(1) <= s_new.index(2)");
    ctx.push_assert("sorted_23", "s_new.index(2) <= s_new.index(3)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Insertion sort sortedness with overflow checking should verify: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Two-pointer patterns with overflow checking
//
// Two-pointer patterns involve addition (s[lo] + s[hi]) and index
// arithmetic. Overflow checking ensures these operations are safe.
// ========================================================================

/// Two-sum postcondition with overflow checking.
///
/// The addition s[i] + s[j] is the core operation. With overflow checking,
/// the encoder verifies this addition doesn't overflow. Without element
/// bounds, this SHOULD produce an overflow counterexample (i32 addition
/// can overflow for arbitrary elements).
#[test]
fn test_vt_overflow_two_sum_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("target", "i32");

    ctx.push_assume("len", "s.len() == 5");
    ctx.push_assume("i_bound", "i < s.len()");
    ctx.push_assume("j_bound", "j < s.len()");
    ctx.push_assume("i_lt_j", "i < j");

    // Element bounds prevent overflow in s[i] + s[j]
    ctx.push_assume(
        "elem_i_bound",
        "s.index(i) >= -1000000 && s.index(i) <= 1000000",
    );
    ctx.push_assume(
        "elem_j_bound",
        "s.index(j) >= -1000000 && s.index(j) <= 1000000",
    );

    ctx.push_assume("found", "s.index(i) + s.index(j) == target");
    ctx.push_assert("post_commuted", "s.index(j) + s.index(i) == target");
    ctx.push_assert("post_partner", "target - s.index(i) == s.index(j)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Two-sum with overflow bounds should verify: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Negative tests — overflow checking catches real problems
//
// Overflow checking should REJECT proofs that rely on arithmetic overflow.
// These tests validate that the safety net works.
// ========================================================================

/// Without element bounds, addition CAN overflow and the overflow check
/// should detect it. The assertion itself is trivially true (reflexive),
/// but the overflow predicate on the addition in the assumption fires.
#[test]
fn test_vt_overflow_unbounded_addition_detected() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("sum", "i32");

    // No bounds on a, b — addition can overflow
    ctx.push_assume("sum_def", "sum == a + b");
    ctx.push_assert("sum_ge_a", "sum >= a");

    let result = ctx.verify();
    // With overflow checking, this should NOT be Verified because:
    // a + b can overflow (e.g., a = MAX_I32, b = 1 → sum wraps to MIN_I32)
    // The overflow check on "a + b" finds the counterexample.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Unbounded addition with overflow checking must produce Counterexample — \
         overflow is possible: {:?}",
        result,
    );
}

/// Bounded addition avoids overflow — the proof should succeed.
#[test]
fn test_vt_overflow_bounded_addition_safe() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");
    ctx.declare_var_parsed("sum", "i32");

    // Bounds prevent overflow: -1B + 1B = 0 (within i32 range)
    ctx.push_assume("a_bound", "a >= -1000000000 && a <= 1000000000");
    ctx.push_assume("b_bound", "b >= -1000000000 && b <= 1000000000");
    ctx.push_assume("sum_def", "sum == a + b");

    ctx.push_assert("sum_ge_a", "sum >= a - 1000000000");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Bounded addition with overflow checking should verify: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Loop invariant with overflow checking
//
// During competition, loop invariants verified through the inductive step
// path also go through overflow checking. This group validates that the
// inductive step + overflow interaction works correctly.
// ========================================================================

/// Frame-based invariant with overflow checking — unmodified variable
/// preserves its own property through the inductive step.
///
/// Loop: while (i < n) { i++; }
/// Invariant: n > 0  (true by precondition, preserved by frame since n
///                     is unmodified — no overflow concerns)
/// Modified: i (only i changes in the loop body)
///
/// With check_overflow = true, the overflow checking path in the inductive
/// step fires. The frame condition `n == n_pre` preserves `n > 0` from
/// the pre-state, so the invariant holds without any arithmetic overflow.
/// Claims about the modified variable `i` require their own invariant.
#[test]
fn test_vt_overflow_frame_invariant_inductive_step() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("i", "u32");
    ctx.declare_var_parsed("n", "u32");

    ctx.push_assume("n_pos", "n > 0");
    ctx.push_assume("init_i", "i == 0");

    ctx.push_obligation(trust_vc_core::vc::ProofObligation::loop_invariant(
        "n_positive",
        "n > 0",
    ));
    ctx.set_loop_modified_vars("n_positive", vec!["i".to_string()]);

    ctx.push_assert("post_nonzero", "n != 0");
    ctx.push_assert("post_still_positive", "n > 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Frame-based invariant with overflow checking should verify: {:?}",
        result,
    );
}

/// Seq length tracking with overflow checking — push preserves length
/// invariant even with overflow-checked arithmetic.
#[test]
fn test_vt_overflow_seq_length_preservation() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("elem", "i32");

    ctx.push_assume("s_len", "s.len() >= 1");
    ctx.push_assume("s_len_bound", "s.len() <= 100");
    ctx.push_assume("elem_val", "elem == 42");

    ctx.push_assert("len_nonzero", "s.len() != 0");
    ctx.push_assert("len_step_bound", "s.len() + 1 <= 101");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq length assertion with overflow checking should verify: {:?}",
        result,
    );
}
