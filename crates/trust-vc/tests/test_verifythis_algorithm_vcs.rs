// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 12 — Complete algorithm VC decomposition.
//!
//! Tiers 1-11 test individual features (arithmetic, quantifiers, Seq, spec axioms).
//! Tier 12 tests the **competition workflow**: decompose an algorithm into
//! Init/Step/Exit verification conditions and verify each one.
//!
//! This is how VerifyThis problems are actually solved:
//!   1. Write the algorithm with loop invariants
//!   2. Generate VCs: Init (precond → inv), Step (inv ∧ guard → inv'), Exit (inv ∧ ¬guard → post)
//!   3. Discharge each VC to the solver
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// ALGORITHM 1: Find Maximum in Sequence (3-element, unrolled)
//
// The canonical VerifyThis warm-up: find the maximum element in an array.
// We start with a fixed-size (n=3) version using manual unrolling to
// validate the VC decomposition pattern before attempting quantified VCs.
//
// Algorithm:
//   max = s[0]; i = 1
//   while i < 3:
//     if s[i] > max: max = s[i]
//     i += 1
//
// Invariant: max >= s[j] for all j < i, and 1 <= i <= 3
// Post: max >= s[j] for all j < 3
// ========================================================================

/// Tier 12a: Find-max Init VC (unrolled, n=3)
///
/// Precondition: s has 3 elements.
/// Initial state: max = s[0], i = 1.
/// Must establish: max >= s[j] for all j < 1 (trivially: max >= s[0]).
#[test]
fn test_vt_tier12a_findmax_init_vc_unrolled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");

    // Precondition
    ctx.push_assume("len", "s.len() == 3");
    // Initial state
    ctx.push_assume("max_init", "max_val == s.index(0)");

    // Init VC: invariant holds at i=1
    // inv: max >= s[j] for all j < 1 → just max >= s[0]
    ctx.push_assert("inv_init", "max_val >= s.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12a: find-max init VC should verify, got: {:?}",
        result,
    );
}

/// Tier 12a: Find-max Init VC with Seq+forall (quantified version)
///
/// Same as above but uses forall quantifier to express the invariant.
/// This validates that the quantified init VC works end-to-end.
#[test]
fn test_vt_tier12a_findmax_init_vc_quantified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("i", "u64");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("max_init", "max_val == s.index(0)");
    ctx.push_assume("i_init", "i == 1");

    // Quantified invariant: forall j < i. max_val >= s[j]
    // At i=1, this is forall j < 1. max_val >= s[j], i.e., just j=0.
    ctx.push_assert(
        "inv_init_q",
        "forall(|j: u64| !(j < i) || max_val >= s.index(j))",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12a: find-max quantified init VC should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// ALGORITHM 1, Step VC: Inductive step for find-max
//
// Assume: inv(i, max) ∧ guard(i < n)
// Body effect: max' = max(max, s[i]), i' = i + 1
// Assert: inv(i', max')
//
// The body effect is modeled as:
//   max_new >= max && max_new >= s[i] && (max_new == max || max_new == s[i])
// ========================================================================

/// Tier 12b: Find-max Step VC (unrolled, iteration i=1→2)
///
/// Inductive hypothesis: max >= s[0] (inv at i=1)
/// Guard: i < 3 (i.e., 1 < 3)
/// Body: max_new = max(max, s[1])
/// Must prove: max_new >= s[0] && max_new >= s[1] (inv at i=2)
#[test]
fn test_vt_tier12b_findmax_step_vc_unrolled_1to2() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("max_new", "i32");

    ctx.push_assume("len", "s.len() == 3");

    // Inductive hypothesis at i=1: max >= s[0]
    ctx.push_assume("inv_ih", "max_val >= s.index(0)");

    // Body effect: max_new = max(max_val, s[1])
    ctx.push_assume("body_ge_old", "max_new >= max_val");
    ctx.push_assume("body_ge_elem", "max_new >= s.index(1)");
    ctx.push_assume("body_is_one", "max_new == max_val || max_new == s.index(1)");

    // Prove invariant at i=2: max_new >= s[0] && max_new >= s[1]
    ctx.push_assert("inv_step_0", "max_new >= s.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12b: find-max step VC (1→2) should verify, got: {:?}",
        result,
    );
}

/// Tier 12b: Find-max Step VC (unrolled, iteration i=2→3)
///
/// Inductive hypothesis: max >= s[0] && max >= s[1]
/// Body: max_new = max(max, s[2])
/// Must prove: max_new >= s[j] for j in 0..3
#[test]
fn test_vt_tier12b_findmax_step_vc_unrolled_2to3() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("max_new", "i32");

    ctx.push_assume("len", "s.len() == 3");

    // Inductive hypothesis at i=2
    ctx.push_assume("inv_ih_0", "max_val >= s.index(0)");
    ctx.push_assume("inv_ih_1", "max_val >= s.index(1)");

    // Body effect
    ctx.push_assume("body_ge_old", "max_new >= max_val");
    ctx.push_assume("body_ge_elem", "max_new >= s.index(2)");
    ctx.push_assume("body_is_one", "max_new == max_val || max_new == s.index(2)");

    // Prove invariant at i=3
    ctx.push_assert("inv_step_0", "max_new >= s.index(0)");
    ctx.push_assert("inv_step_1", "max_new >= s.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12b: find-max step VC (2→3) should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// ALGORITHM 1, Exit VC: Postcondition from invariant + negated guard
// ========================================================================

/// Tier 12c: Find-max Exit VC (unrolled)
///
/// Invariant at loop exit: max >= s[j] for all j < 3
/// DISCRIMINATING: Asserts negated form !(s[j] > max) instead of identical
/// max >= s[j]. Requires solver to reason about >=  ↔  !(>) equivalence. (#2084 audit)
#[test]
fn test_vt_tier12c_findmax_exit_vc_unrolled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");

    ctx.push_assume("len", "s.len() == 3");

    // Invariant at exit: max >= all elements
    ctx.push_assume("inv_0", "max_val >= s.index(0)");
    ctx.push_assume("inv_1", "max_val >= s.index(1)");
    ctx.push_assume("inv_2", "max_val >= s.index(2)");

    // Postcondition in negated form: !(s[j] > max) ≡ max >= s[j]
    // Requires solver to handle negation of strict comparison
    ctx.push_assert("post_0", "!(s.index(0) > max_val)");
    ctx.push_assert("post_1", "!(s.index(1) > max_val)");
    ctx.push_assert("post_2", "!(s.index(2) > max_val)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12c: find-max exit VC should verify, got: {:?}",
        result,
    );
}

/// Tier 12c: Find-max Exit VC with quantified postcondition
///
/// Tests the combination: assumed invariant (unrolled) → quantified postcondition.
#[test]
fn test_vt_tier12c_findmax_exit_vc_quantified_post() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("n_eq", "n == 3");

    // Assumed invariant at exit (unrolled)
    ctx.push_assume("inv_0", "max_val >= s.index(0)");
    ctx.push_assume("inv_1", "max_val >= s.index(1)");
    ctx.push_assume("inv_2", "max_val >= s.index(2)");

    // Quantified postcondition
    ctx.push_assert(
        "post_all",
        "forall(|j: u64| !(j < n) || max_val >= s.index(j))",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12c: find-max exit VC with quantified post should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// ALGORITHM 1, Negative tests: Wrong postconditions must be rejected
// ========================================================================

/// Tier 12d: Find-max negative — wrong postcondition (max > all, not max >= all)
///
/// max >= s[j] does NOT imply max > s[j] (equality case).
#[test]
fn test_vt_tier12d_findmax_wrong_postcondition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("inv_0", "max_val >= s.index(0)");
    ctx.push_assume("inv_1", "max_val >= s.index(1)");
    ctx.push_assume("inv_2", "max_val >= s.index(2)");

    // Wrong: max STRICTLY greater than all elements
    // Counterexample: all elements equal
    ctx.push_assert("wrong_post", "max_val > s.index(0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 12d SOUNDNESS: max >= s[j] should not prove max > s[j] (e.g. s=[5,5,5], max_val=5), got: {:?}",
        result,
    );
}

// ========================================================================
// ALGORITHM 1, Quantified Step VC: The key competition pattern
//
// This tests whether ay-dpll can handle the inductive step with
// quantified invariants — the core of every VerifyThis proof.
//
// Assume: forall j < i. max >= s[j]  (ind. hyp — universal in assumption)
//         i < n                       (guard)
//         max_new >= max              (body: monotone)
//         max_new >= s[i]            (body: covers new element)
// Assert: forall j < i+1. max_new >= s[j]  (inv preserved)
// ========================================================================

/// Tier 12e: Find-max quantified Step VC
///
/// This is the hardest VC for ay-dpll: it requires instantiating the
/// assumed universal at the Skolem constant from the assertion.
/// If this verifies, trust_vc can handle the core VerifyThis pattern.
#[test]
fn test_vt_tier12e_findmax_step_vc_quantified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("max_val", "i32");
    ctx.declare_var_parsed("max_new", "i32");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("i_new", "u64");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");
    ctx.push_assume("n_le3", "n <= 3");

    // Inductive hypothesis (universal in assumption context)
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_lt_n", "i < n");
    ctx.push_assume(
        "inv_ih",
        "forall(|j: u64| !(j < i) || max_val >= s.index(j))",
    );

    // Body effect: max_new = max(max_val, s[i])
    ctx.push_assume("body_ge_old", "max_new >= max_val");
    ctx.push_assume("body_ge_elem", "max_new >= s.index(i)");

    // i increments
    ctx.push_assume("i_step", "i_new == i + 1");

    // Assert: invariant preserved at i_new
    ctx.push_assert(
        "inv_preserved",
        "forall(|j: u64| !(j < i_new) || max_new >= s.index(j))",
    );

    let result = ctx.verify();
    // ay-dpll handles this by:
    // 1. Skolemize the assertion → j_sk < i_new && max_new < s[j_sk]
    // 2. Instantiate assumed universal at j_sk
    // 3. Case split j_sk < i vs j_sk == i, derive contradiction in both
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12e: quantified step VC should verify — this is the core \
         VerifyThis pattern (assumed universal + Skolemized assertion), got: {:?}",
        result,
    );
}

// ========================================================================
// ALGORITHM 2: Linear Search (is-sorted check)
//
// Simpler than find-max: verify that a sequence is sorted.
// No max tracking needed — just check adjacent pairs.
//
// Algorithm:
//   result = true
//   for i in 0..n-1:
//     if s[i] > s[i+1]: result = false; break
//
// Simplified VC: if all adjacent pairs are sorted, then forall i<j. s[i]<=s[j]
// ========================================================================

/// Tier 12f: Is-sorted — adjacent pairs imply global order (3 elements)
///
/// Assume: s[0] <= s[1] && s[1] <= s[2]
/// Assert: s[0] <= s[2] (transitivity)
///
/// This is the exit VC for an is-sorted check.
#[test]
fn test_vt_tier12f_issorted_transitivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("sorted_01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted_12", "s.index(1) <= s.index(2)");

    // Transitivity: s[0] <= s[2]
    ctx.push_assert("transitive", "s.index(0) <= s.index(2)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12f: sorted transitivity should verify, got: {:?}",
        result,
    );
}

/// Tier 12f: Is-sorted negative — unsorted pair detected
///
/// Assume: s[0] <= s[1] but s[1] > s[2] (not sorted)
/// Assert: s[0] <= s[2] should NOT verify
#[test]
fn test_vt_tier12f_issorted_negative_unsorted() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("sorted_01", "s.index(0) <= s.index(1)");
    ctx.push_assume("unsorted_12", "s.index(1) > s.index(2)");

    ctx.push_assert("transitive_false", "s.index(0) <= s.index(2)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 12f SOUNDNESS: an unsorted witness (e.g. s=[0,1,-1]) must not prove transitivity, got: {:?}",
        result,
    );
}

// ========================================================================
// ALGORITHM 3: Partial Sum (accumulation pattern)
//
// Algorithm:
//   sum = 0
//   for i in 0..n:
//     sum += s[i]
//
// Invariant: sum == s[0] + s[1] + ... + s[i-1]
// This exercises the additive accumulation VC pattern.
// ========================================================================

/// Tier 12g: Partial sum — init VC
///
/// sum = 0, i = 0. Invariant: sum == sum of first 0 elements = 0.
#[test]
fn test_vt_tier12g_partial_sum_init_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("sum_val", "i32");

    ctx.push_assume("sum_init", "sum_val == 0");
    ctx.push_assert("inv_init_nonneg", "sum_val >= 0");
    ctx.push_assert("inv_init_nonpos", "sum_val <= 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12g: partial sum init VC should verify, got: {:?}",
        result,
    );
}

/// Tier 12g: Partial sum — step VC (concrete, 2 iterations)
///
/// After iteration 0: sum == s[0]
/// Body: sum_new = sum + s[1]
/// Assert: sum_new == s[0] + s[1]
#[test]
fn test_vt_tier12g_partial_sum_step_vc() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("sum_val", "i32");
    ctx.declare_var_parsed("sum_new", "i32");

    ctx.push_assume("len", "s.len() == 3");
    // Bound to avoid overflow
    ctx.push_assume("elem_bound_0", "s.index(0) > -1000 && s.index(0) < 1000");
    ctx.push_assume("elem_bound_1", "s.index(1) > -1000 && s.index(1) < 1000");

    // Inductive hypothesis: sum == s[0] after iteration 0
    ctx.push_assume("inv_ih", "sum_val == s.index(0)");

    // Body: sum_new = sum + s[1]
    ctx.push_assume("body", "sum_new == sum_val + s.index(1)");

    // Assert: sum_new == s[0] + s[1]
    ctx.push_assert("inv_step", "sum_new == s.index(0) + s.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 12g: partial sum step VC should verify, got: {:?}",
        result,
    );
}

// Dutch National Flag, partial sum exit VC, and other VerifyThis algorithms
// can be added as separate Tier 13+ tests when competition-specific problem
// modeling is needed.
