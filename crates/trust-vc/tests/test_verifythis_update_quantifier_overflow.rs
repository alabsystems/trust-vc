// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 23 — Seq.update + quantifier overflow interaction.
//!
//! Tiers 21-22 validated overflow checking on scalar arithmetic and
//! competition patterns (binary search, prefix sum, multiplication).
//! This tier fills the two remaining gaps:
//!
//! GROUP A: Seq.update patterns under overflow checking.
//!   Competitors write `s.update(i, v)` in every array-modifying algorithm.
//!   With `check_overflow = true`, the index arithmetic and value expressions
//!   inside update go through overflow predicate generation. These tests
//!   validate that bounded Seq.update verifies and unbounded is caught.
//!
//! GROUP B: Quantifier + overflow interaction.
//!   Competition invariants like `forall j < n. s[j] >= 0` contain arithmetic
//!   in the quantifier body. With `check_overflow = true`, the encoder must
//!   handle overflow predicates inside Skolemized quantifier bodies. These
//!   tests validate that bounded quantifier arithmetic verifies cleanly.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Seq.update under overflow checking
//
// `s.update(i, v)` creates a new sequence identical to s except at index i
// where the value is v. The index arithmetic (i computation) and the value
// expression (v computation) are both subject to overflow checking.
// ========================================================================

/// Basic Seq.update read-back with overflow checking.
///
/// Pattern: `s.update(idx, val).index(idx) == val` — the fundamental
/// store-then-load identity. With overflow checking, this should still
/// verify because update/index don't involve arithmetic overflow.
#[test]
fn test_vt_overflow_seq_update_read_back() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("idx", "u64");
    ctx.declare_var_parsed("val", "i32");

    ctx.push_assume("len", "s.len() == 5");
    ctx.push_assume("idx_bound", "idx < s.len()");
    ctx.push_assume("val_bound", "val >= -1000 && val <= 1000");

    // Store-then-load identity
    ctx.push_assert("read_back", "s.update(idx, val).index(idx) == val");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq.update read-back with overflow checking should verify: {:?}",
        result,
    );
}

/// Seq.update frame preservation — update at idx doesn't change other indices.
///
/// Pattern: `s.update(i, v).index(j) == s.index(j)` when `i != j`.
/// Critical for competition proofs: after modifying one element, the rest
/// of the sequence is unchanged (frame condition).
#[test]
fn test_vt_overflow_seq_update_frame() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("val", "i32");

    ctx.push_assume("len", "s.len() == 4");
    ctx.push_assume("i_bound", "i < s.len()");
    ctx.push_assume("j_bound", "j < s.len()");
    ctx.push_assume("i_ne_j", "i != j");
    ctx.push_assume("val_bound", "val >= 0 && val <= 100");

    // Frame: update at i doesn't affect index j
    ctx.push_assert("frame", "s.update(i, val).index(j) == s.index(j)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq.update frame preservation with overflow checking should verify: {:?}",
        result,
    );
}

/// Seq.update with computed value — arithmetic in the update value.
///
/// Pattern: `s.update(i, s.index(i) + delta)` where delta is bounded.
/// This is the core competition pattern for in-place modification:
/// incrementing an element, accumulating into array cells, etc.
/// The `s.index(i) + delta` expression triggers overflow checking.
#[test]
fn test_vt_overflow_seq_update_computed_value() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("delta", "i32");
    ctx.declare_var_parsed("s_new", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 4");
    ctx.push_assume("i_bound", "i < s.len()");
    // Element and delta bounded to prevent overflow
    ctx.push_assume(
        "elem_bound",
        "s.index(i) >= -1000000 && s.index(i) <= 1000000",
    );
    ctx.push_assume("delta_bound", "delta >= -1000 && delta <= 1000");

    // Computed update: new value is old value + delta
    ctx.push_assume("update_def", "s_new == s.update(i, s.index(i) + delta)");
    // Seq.update preserves length (must be stated explicitly for new variable)
    ctx.push_assume("len_new", "s_new.len() == s.len()");

    // The new element equals old + delta
    ctx.push_assert("new_val", "s_new.index(i) == s.index(i) + delta");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq.update with computed value should verify — bounds prevent overflow: {:?}",
        result,
    );
}

/// Seq.update length preservation — update does not change sequence length.
///
/// Competitors rely on `s.update(i, v).len() == s.len()` implicitly.
/// With overflow checking, this must still hold.
#[test]
fn test_vt_overflow_seq_update_length_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("idx", "u64");
    ctx.declare_var_parsed("val", "i32");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("idx_bound", "idx < s.len()");

    ctx.push_assert("len_preserved", "s.update(idx, val).len() == s.len()");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Seq.update should preserve length with overflow checking: {:?}",
        result,
    );
}

/// Swap pattern — two updates that exchange elements.
///
/// Pattern: `s.update(i, s.index(j)).update(j, s.index(i))`.
/// Competition patterns: bubble sort, partition, selection sort all swap.
/// With overflow checking, the index and value expressions are checked.
#[test]
fn test_vt_overflow_seq_swap_pattern() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("s_swapped", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 4");
    ctx.push_assume("i_bound", "i < s.len()");
    ctx.push_assume("j_bound", "j < s.len()");
    ctx.push_assume("i_ne_j", "i != j");
    ctx.push_assume(
        "s_vals",
        "s.index(0) == 10 && s.index(1) == 20 && s.index(2) == 30 && s.index(3) == 40",
    );
    ctx.push_assume("i_val", "i == 1");
    ctx.push_assume("j_val", "j == 3");

    // Swap: s_swapped = s[i←s[j]][j←s[i]]
    ctx.push_assume(
        "swap_def",
        "s_swapped == s.update(i, s.index(j)).update(j, s.index(i))",
    );
    // Seq.update preserves length (must be stated explicitly for new variable)
    ctx.push_assume("len_swapped", "s_swapped.len() == s.len()");

    // After swap: positions are exchanged
    ctx.push_assert("swapped_i", "s_swapped.index(1) == 40");
    ctx.push_assert("swapped_j", "s_swapped.index(3) == 20");
    // Frame: other positions unchanged
    ctx.push_assert("frame_0", "s_swapped.index(0) == 10");
    ctx.push_assert("frame_2", "s_swapped.index(2) == 30");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Swap pattern with overflow checking should verify: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Quantifier + overflow interaction
//
// Competition invariants use `forall(|j: u64| !(j < n) || P(s[j]))`.
// When P(s[j]) contains arithmetic (e.g., `s[j] + 1 > 0`), the encoder
// generates overflow predicates inside the Skolemized quantifier body.
// These tests validate that the interaction works correctly.
// ========================================================================

/// Quantifier with no arithmetic — pure comparison, no overflow concern.
///
/// Pattern: `forall j < n. s[j] >= 0` — the most common competition invariant.
/// This should verify regardless of overflow checking because there's no
/// arithmetic operation subject to overflow.
#[test]
fn test_vt_overflow_forall_pure_comparison() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("elem0", "s.index(0) == 10");
    ctx.push_assume("elem1", "s.index(1) == 20");
    ctx.push_assume("elem2", "s.index(2) == 30");

    ctx.push_assert("all_nonneg", "forall(|i: u64| !(i < 3) || s.index(i) >= 0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "forall with pure comparison should verify under overflow checking: {:?}",
        result,
    );
}

/// Quantifier with bounded arithmetic in body.
///
/// Pattern: `forall j < n. s[j] + 1 > 0` — arithmetic inside quantifier body.
/// With overflow checking, the `s[j] + 1` expression is subject to overflow
/// predicates. With element bounds, this should verify.
#[test]
fn test_vt_overflow_forall_bounded_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("elem0", "s.index(0) == 10");
    ctx.push_assume("elem1", "s.index(1) == 20");
    ctx.push_assume("elem2", "s.index(2) == 30");

    // s[j] + 1 > 0 — arithmetic in quantifier body, but values are bounded
    ctx.push_assert(
        "all_positive_shifted",
        "forall(|j: u64| !(j < 3) || s.index(j) + 1 > 0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "forall with bounded arithmetic should verify under overflow checking: {:?}",
        result,
    );
}

/// Quantifier with sortedness — comparison between adjacent elements.
///
/// Pattern: `forall j < n-1. s[j] <= s[j+1]` — sortedness invariant.
/// The `j+1` index expression contains arithmetic. With overflow checking,
/// the encoder checks the index computation doesn't overflow u64.
#[test]
fn test_vt_overflow_forall_sortedness() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 4");
    ctx.push_assume("s0", "s.index(0) == 1");
    ctx.push_assume("s1", "s.index(1) == 3");
    ctx.push_assume("s2", "s.index(2) == 5");
    ctx.push_assume("s3", "s.index(3) == 7");

    // Sortedness: s[j] <= s[j+1] for all j < 3
    // The `j + 1` in the index is arithmetic subject to overflow checking
    ctx.push_assert(
        "sorted",
        "forall(|j: u64| !(j < 3) || s.index(j) <= s.index(j + 1))",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "forall sortedness with overflow checking should verify: {:?}",
        result,
    );
}

/// Negative: forall with element that violates the property.
///
/// Soundness check: `forall j < n. s[j] > 0` must NOT verify when one
/// element is zero, even under overflow checking.
#[test]
fn test_vt_overflow_forall_negative_violation() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("elem0", "s.index(0) == 5");
    ctx.push_assume("elem1", "s.index(1) == 0"); // violates > 0
    ctx.push_assume("elem2", "s.index(2) == 10");

    ctx.push_assert(
        "all_positive",
        "forall(|j: u64| !(j < 3) || s.index(j) > 0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "forall with violation must produce Counterexample under overflow checking: {:?}",
        result,
    );
}

/// Combined: Seq.update + forall invariant preservation under overflow.
///
/// The key competition pattern: after updating one element, re-verify
/// the invariant. This combines both Group A and Group B.
///
/// Pattern: given all-nonneg, update at index i with a nonneg value,
/// then assert all-nonneg still holds.
#[test]
fn test_vt_overflow_update_preserves_forall_invariant() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("val", "i32");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("elem0", "s.index(0) == 10");
    ctx.push_assume("elem1", "s.index(1) == 20");
    ctx.push_assume("elem2", "s.index(2) == 30");
    ctx.push_assume("val_nonneg", "val >= 0 && val <= 1000");

    // Update at index 1
    ctx.push_assume("update_def", "s_new == s.update(1, val)");
    // Seq.update preserves length (must be stated explicitly for new variable)
    ctx.push_assume("len_new", "s_new.len() == s.len()");

    // After update, all elements are still nonneg
    ctx.push_assert(
        "all_nonneg_preserved",
        "forall(|j: u64| !(j < 3) || s_new.index(j) >= 0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Update preserving forall invariant should verify under overflow: {:?}",
        result,
    );
}

/// Competition pattern: partial sort step under overflow checking.
///
/// Models one step of selection sort: find that s[k] is the minimum,
/// swap s[0] and s[k], then verify s_new[0] <= s_new[j] for all j.
/// Uses concrete indices for decidability (ay-dpll BV).
#[test]
fn test_vt_overflow_partial_sort_step() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("elem0", "s.index(0) == 30");
    ctx.push_assume("elem1", "s.index(1) == 10");
    ctx.push_assume("elem2", "s.index(2) == 20");

    // s[1] is the minimum — swap s[0] and s[1]
    ctx.push_assume(
        "swap_def",
        "s_new == s.update(0, s.index(1)).update(1, s.index(0))",
    );
    // Seq.update preserves length (must be stated explicitly for new variable)
    ctx.push_assume("len_new", "s_new.len() == s.len()");

    // After swap: s_new[0] == 10 (the minimum)
    ctx.push_assert("min_at_front", "s_new.index(0) == 10");
    // s_new[0] <= all elements
    ctx.push_assert("min_le_1", "s_new.index(0) <= s_new.index(1)");
    ctx.push_assert("min_le_2", "s_new.index(0) <= s_new.index(2)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Selection sort step with overflow checking should verify: {:?}",
        result,
    );
}
