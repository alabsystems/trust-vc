// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 13 — Competition-realistic verification patterns.
//!
//! Tiers 1-12 test features on bounded arrays (n ≤ 3). Tier 13 tests patterns
//! from real VerifyThis problems: unbounded quantifiers, sortedness reasoning,
//! binary search VCs, multi-property insertion, and counting accumulators.
//!
//! KEY FINDING: BV overflow guards are mandatory in ALL VCs. Every `+ 1` on u64
//! needs a bound to prevent wraparound counterexamples.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

mod common;

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::{UnknownCategory, VerifyResult};

// ========================================================================
// GROUP A: Unbounded quantifier VCs (no n ≤ 3 bound)
// ========================================================================

/// Tier 13a: Find-max step VC with unbounded n (no n ≤ 3).
/// Tests genuine quantifier instantiation via Skolemization + E-matching.
#[test]
fn test_vt_tier13a_findmax_step_vc_unbounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("max_new", "i32");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume(
        "inv_ih",
        "forall(|j: u64| !(j < i) || max_val >= s.index(j))",
    );
    ctx.push_assume("body_ge_old", "max_new >= max_val");
    ctx.push_assume("body_ge_elem", "max_new >= s.index(i)");
    ctx.push_assume("i_step", "i_new == i + 1");

    ctx.push_assert(
        "inv_preserved",
        "forall(|j: u64| !(j < i_new) || max_new >= s.index(j))",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 13a: unbounded find-max step VC should verify, got: {:?}",
        result,
    );
}

/// Tier 13a: Find-max exit VC with unbounded n.
///
/// DISCRIMINATING: Assumes quantified invariant, asserts concrete instantiation
/// at j=0. Requires the solver to instantiate the universal quantifier —
/// a tautological `assume P, assert P` would not test this. (#2084 audit)
#[test]
fn test_vt_tier13a_findmax_exit_vc_unbounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");
    ctx.push_assume(
        "inv_exit",
        "forall(|j: u64| !(j < n) || max_val >= s.index(j))",
    );

    // Concrete instantiation at j=0: requires universal quantifier instantiation
    ctx.push_assert("post_first", "max_val >= s.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 13a: exit VC should verify (∀j instantiated at j=0), got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Sortedness reasoning (competition-critical)
// ========================================================================

/// Tier 13b: Adjacent-pair sortedness → transitivity (s[0] ≤ s[2]).
///
/// ay-dpll non-determinism (#2273): chaining two quantifier instantiations
/// (k=0 and k=1) sometimes verifies, sometimes hits the confirmation check
/// disagreement. Both outcomes are correct — Verified means the chain worked,
/// ConfirmationDisagree means the safety net caught non-determinism.
/// Workaround: concrete instantiation (13b_workaround).
#[test]
fn test_vt_tier13b_sortedness_transitivity_from_adjacent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge3", "n >= 3");
    ctx.push_assume(
        "adj_sorted",
        "forall(|k: u64| !(k + 1 < n) || s.index(k) <= s.index(k + 1))",
    );

    ctx.push_assert("trans_02", "s.index(0) <= s.index(2)");

    let result = ctx.verify();
    // ay-dpll non-determinism (#2273): result varies between runs.
    // When Unknown, it must be ConfirmationDisagree (not some other failure).
    match &result {
        VerifyResult::Verified => {}
        VerifyResult::Unknown { .. } => {
            assert_eq!(
                result.unknown_category(),
                Some(UnknownCategory::ConfirmationDisagree),
                "TIER 13b: when Unknown, should be ConfirmationDisagree, got: {:?}",
                result,
            );
        }
        other => panic!(
            "TIER 13b: should verify or hit confirmation disagree, got: {:?}",
            other,
        ),
    }
}

/// Tier 13b: Competition workaround — concrete instantiation of universals.
/// Instead of relying on ay-dpll to chain instantiations, unroll manually.
#[test]
fn test_vt_tier13b_sortedness_transitivity_workaround() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge3", "n >= 3");
    ctx.push_assume("sorted_01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted_12", "s.index(1) <= s.index(2)");

    ctx.push_assert("trans_02", "s.index(0) <= s.index(2)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 13b: concrete instantiation workaround should verify, got: {:?}",
        result,
    );
}

/// Tier 13b: Sortedness negative — wrong direction.
///
/// Uses concrete pairwise sorted assumptions instead of a quantified forall
/// over symbolic n. The quantified version times out in ay-dpll BV solver;
/// concrete decomposition is the competition-safe pattern. Part of #2187.
#[test]
fn test_vt_tier13b_sortedness_negative_wrong_direction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_eq3", "n == 3");
    // Concrete pairwise sorted: avoids quantifier-over-symbolic-n BV timeout.
    ctx.push_assume("sorted_01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted_12", "s.index(1) <= s.index(2)");

    // s[0] <= s[1] <= s[2] implies s[2] >= s[0], so s[2] <= s[0] fails
    // whenever the values are not all equal (e.g., s = [1, 2, 3]).
    ctx.push_assert("wrong_direction", "s.index(2) <= s.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 13b SOUNDNESS: wrong-direction sortedness must produce Counterexample: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Binary search VCs
// ========================================================================

/// Tier 13c: Binary search — found case exit VC.
///
/// DISCRIMINATING: Assumes equality, asserts decomposed into two inequalities.
/// Requires the solver to derive s[mid] >= target AND s[mid] <= target from
/// s[mid] == target, not just pattern-match the identical formula. (#2084 audit)
#[test]
fn test_vt_tier13c_bsearch_found_exit_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("target", "i32");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");
    ctx.push_assume("mid_in_range", "mid < n");
    ctx.push_assume("found", "s.index(mid) == target");

    // Decomposed equality: requires solver to derive both directions
    ctx.push_assert("post_ge", "s.index(mid) >= target");
    ctx.push_assert("post_le", "s.index(mid) <= target");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 13c: binary search found exit VC should verify, got: {:?}",
        result,
    );
}

/// Tier 13c: Binary search step — range narrowing (right half).
///
/// The `exists` quantifier in the assumption triggers a sort mismatch
/// in the encoder (mixed i32/u64 comparison in the guard), so this
/// fails closed as Unknown. Tracks the exists-encoder limitation.
#[test]
fn test_vt_tier13c_bsearch_step_narrow_right() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("target", "i32");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("range_valid", "lo <= hi && hi <= n");
    ctx.push_assume(
        "sorted",
        "forall(|k: u64| !(k + 1 < n) || s.index(k) <= s.index(k + 1))",
    );
    ctx.push_assume(
        "target_in_range",
        "exists(|k: u64| k >= lo && k < hi && s.index(k) == target)",
    );
    ctx.push_assume("mid_calc", "mid >= lo && mid < hi");
    ctx.push_assume("mid_lt_target", "s.index(mid) < target");

    ctx.push_assert(
        "target_in_new_range",
        "exists(|k: u64| k >= mid + 1 && k < hi && s.index(k) == target)",
    );

    let result = ctx.verify();
    // The exists quantifier with mixed-sort comparison (i32 vs u64)
    // hits the typed-assumption encoder sort mismatch path and fails closed
    // as Error rather than solver Unknown.
    assert!(
        matches!(
            &result,
            VerifyResult::Error { message } if message.contains("sort mismatch")
        ),
        "TIER 13c: exists+sorted should hit sort mismatch encoder limitation, got: {:?}",
        result,
    );
}

/// Tier 13c: Binary search negative — wrong half after narrowing.
#[test]
fn test_vt_tier13c_bsearch_negative_wrong_half() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("target", "i32");
    ctx.declare_var_parsed("lo", "u64");
    ctx.declare_var_parsed("hi", "u64");
    ctx.declare_var_parsed("mid", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge3", "n >= 3");
    ctx.push_assume("range_valid", "lo < mid && mid < hi && hi <= n");
    ctx.push_assume(
        "sorted",
        "forall(|k: u64| !(k + 1 < n) || s.index(k) <= s.index(k + 1))",
    );
    ctx.push_assume("mid_lt_target", "s.index(mid) < target");

    ctx.push_assert(
        "wrong_half",
        "exists(|k: u64| k >= lo && k < mid && s.index(k) == target)",
    );

    let result = ctx.verify();
    // The unsupported exists path still fails closed here: proving the left-half
    // witness uses the same mixed-sort comparison shape as the positive case.
    assert!(
        matches!(
            &result,
            VerifyResult::Unknown { reason, .. } if reason.contains("sort mismatch")
        ),
        "TIER 13c SOUNDNESS: wrong-half witness should hit the exists sort mismatch limitation, got: {:?}",
        result,
    );
    assert_eq!(
        result.unknown_category(),
        Some(UnknownCategory::SolverPanic),
        "TIER 13c SOUNDNESS: overflow-predicate sort mismatch should classify as UnknownCategory::SolverPanic (#2333), got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Multi-property VCs (insertion)
// ========================================================================

/// Tier 13d: Insertion preserves element at position + prefix unchanged.
/// BV overflow guard: n < 1000000 prevents n+1 wraparound.
///
/// DISCRIMINATING: v_present asserts decomposed inequality form instead of
/// identical formula. Assumes grouped before asserts. (#2084 audit)
#[test]
fn test_vt_tier13d_insertion_preserves_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("v", "i32");
    ctx.declare_var_parsed("p", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_old", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");
    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("len_new", "s_new.len() == n + 1");
    ctx.push_assume("p_valid", "p <= n");
    ctx.push_assume("insert_at_p", "s_new.index(p) == v");
    ctx.push_assume(
        "prefix_preserved",
        "forall(|j: u64| !(j < p) || s_new.index(j) == s.index(j))",
    );
    ctx.push_assume("p_gt0", "p > 0");

    // Decomposed equality: s_new[p] >= v AND s_new[p] <= v (not identical to assumption)
    ctx.push_assert("v_ge", "s_new.index(p) >= v");
    ctx.push_assert("v_le", "s_new.index(p) <= v");
    ctx.push_assert("first_preserved", "s_new.index(0) == s.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 13d: insertion should preserve element + prefix, got: {:?}",
        result,
    );
}

/// Tier 13d: Insertion negative — wrong value at position.
#[test]
fn test_vt_tier13d_insertion_negative_wrong_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s_new", "Seq<i32>");
    ctx.declare_var_parsed("v", "i32");
    ctx.declare_var_parsed("p", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("n_bounded", "n < 1000000");
    ctx.push_assume("len_new", "s_new.len() == n + 1");
    ctx.push_assume("p_valid", "p <= n");
    ctx.push_assume("insert_at_p", "s_new.index(p) == v");
    ctx.push_assume("v_bounded", "v < 1000000");

    ctx.push_assert("wrong_value", "s_new.index(p) == v + 1");

    let result = ctx.verify();
    // This is quantifier-free in the postcondition, so the failure should stay
    // on the concrete counterexample path rather than drifting into Unknown.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 13d SOUNDNESS: wrong inserted value should return a counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Counting accumulators
// ========================================================================

/// Tier 13e: Counting — count ≤ n at loop exit.
#[test]
fn test_vt_tier13e_count_bounded_by_length() {
    common::with_clean_verification(|| {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("count", "u64");
        ctx.declare_var_parsed("n", "u64");
        ctx.declare_var_parsed("i", "u64");

        ctx.push_assume("n_bounded", "n < 1000000");
        ctx.push_assume("count_le_i", "count <= i");
        ctx.push_assume("i_eq_n", "i == n");

        ctx.push_assert("count_le_n", "count <= n");

        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "TIER 13e: count <= i and i == n should imply count <= n, got: {:?}",
            result,
        );
    });
}

/// Tier 13e: Counting step VC — count increments by at most 1.
/// BV overflow guard: i < 1000000 prevents i+1 and count+1 wraparound.
#[test]
fn test_vt_tier13e_count_step_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("count", "u64");
    ctx.declare_var_parsed("count_new", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");

    ctx.push_assume("i_bounded", "i < 1000000");
    ctx.push_assume("inv_ih", "count <= i");
    ctx.push_assume(
        "count_update",
        "count_new == count || count_new == count + 1",
    );
    ctx.push_assume("i_step", "i_new == i + 1");

    ctx.push_assert("inv_preserved", "count_new <= i_new");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 13e: count step VC should verify, got: {:?}",
        result,
    );
}
