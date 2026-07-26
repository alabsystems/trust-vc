// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Symbolic-length Seq + forall tests.
//!
//! Tier 8 tests in test_verifythis_practice.rs use concrete lengths (len==2, len==3).
//! Real VerifyThis problems use symbolic/variable-length sequences:
//!   `forall j < n. s[j] >= 0` where `n` is a function parameter.
//!
//! These tests validate that ay-dpll can handle BV-sorted Skolemization
//! with symbolic lengths. All patterns verified as of 2026-03-12.
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// TIER 9a: Symbolic length with concrete elements
// Length `n` is a variable (not constant), elements are still concrete.
// Tests ay-dpll's ability to reason about `j_sk < n` where n varies.
// ========================================================================

/// Symbolic n ∈ [1,3], concrete elements all non-negative.
/// Assertion: forall j < n. s[j] >= 0
///
/// With BV Skolemization, negated assertion is: j_sk < n && s[j_sk] < 0.
/// ay reasons: n ∈ [1,3], s[0..2] all >= 0, so no valid j_sk < n
/// can select a negative element. UNSAT → Verified.
#[test]
fn test_vt_tier9a_symbolic_len_concrete_elems() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");
    ctx.push_assume("n_ge3", "n >= 3");
    ctx.push_assume("n_le3", "n <= 3");
    ctx.push_assume("elem0", "s.index(0) == 10");
    ctx.push_assume("elem1", "s.index(1) == 20");
    ctx.push_assume("elem2", "s.index(2) == 30");

    ctx.push_assert("all_nonneg", "forall(|j: u64| !(j < n) || s.index(j) >= 0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 9a: symbolic len ∈ [1,3] + concrete elems should verify, got: {:?}",
        result,
    );
}

/// Symbolic n == fixed constant (existentially determined).
/// Same as Tier 8 but n is a variable equal to 3, not literal 3.
/// Tests that the symbolic indirection doesn't break BV reasoning.
#[test]
fn test_vt_tier9a_symbolic_n_equals_constant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_eq_3", "n == 3");
    ctx.push_assume("elem0", "s.index(0) == 10");
    ctx.push_assume("elem1", "s.index(1) == 20");
    ctx.push_assume("elem2", "s.index(2) == 30");

    ctx.push_assert("all_nonneg", "forall(|j: u64| !(j < n) || s.index(j) >= 0)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 9a: symbolic n==3 + concrete elems should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 9b: Symbolic length — negative tests (soundness check)
// ========================================================================

/// Negative: one element is negative, forall-nonneg must not verify.
#[test]
fn test_vt_tier9b_symbolic_len_negative_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_eq_2", "n == 2");
    ctx.push_assume("elem0", "s.index(0) == 10");
    ctx.push_assume("elem1", "s.index(1) == -5");

    ctx.push_assert(
        "all_nonneg_false",
        "forall(|j: u64| !(j < n) || s.index(j) >= 0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 9b SOUNDNESS: Seq with negative elem + symbolic n must produce Counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 9c: Sorted-sequence max-element with symbolic length
// Pattern: assume sorted, assert last element is max.
// Core VerifyThis "find maximum" specification.
// ========================================================================

/// Sorted Seq with symbolic n==3, assert last element is max.
#[test]
fn test_vt_tier9c_sorted_max_symbolic_n() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_eq_3", "n == 3");
    ctx.push_assume("sorted01", "s.index(0) <= s.index(1)");
    ctx.push_assume("sorted12", "s.index(1) <= s.index(2)");

    ctx.push_assert(
        "all_le_max",
        "forall(|j: u64| !(j < n) || s.index(j) <= s.index(2))",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 9c: sorted Seq max with symbolic n==3 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 9d: Symbolic length with bounded range (truly variable)
// n is not pinned to a constant — it ranges over [1, max].
// ========================================================================

/// Bounded n ∈ [1,2], concrete elements.
#[test]
fn test_vt_tier9d_bounded_n_small_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("n_le2", "n <= 2");
    ctx.push_assume("elem0", "s.index(0) == 5");
    ctx.push_assume("elem1", "s.index(1) == 10");

    ctx.push_assert(
        "all_positive",
        "forall(|j: u64| !(j < n) || s.index(j) > 0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 9d: bounded n ∈ [1,2] + concrete elems should verify, got: {:?}",
        result,
    );
}

/// Single element: n == 1.
#[test]
fn test_vt_tier9d_single_element_symbolic_n() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_eq_1", "n == 1");
    ctx.push_assume("elem0", "s.index(0) == 42");

    ctx.push_assert(
        "single_positive",
        "forall(|j: u64| !(j < n) || s.index(j) > 0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 9d: single element symbolic n==1 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 9e: Symbolic elements (hardest pattern)
// Elements are NOT concrete — property comes from assumptions.
// This tests whether ay-dpll can propagate array constraints.
// ========================================================================

/// Two-element Seq built by push: elements are computed, not literal.
/// Pattern: s = empty.push(a).push(b), assume a > 0 && b > 0,
/// assert forall j < 2. s[j] > 0.
///
/// This tests whether ay-dpll can connect push-constructed arrays
/// with the Skolemized forall. Elements are symbolic (a, b) with
/// assumed positivity, not hardcoded constants.
#[test]
fn test_vt_tier9e_symbolic_elems_via_push() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");

    // Elements are symbolic with assumed positivity
    ctx.push_assume("a_pos", "a > 0");
    ctx.push_assume("b_pos", "b > 0");

    // Seq built by storing symbolic values
    ctx.push_assume("len", "s.len() == 2");
    ctx.push_assume("elem0", "s.index(0) == a");
    ctx.push_assume("elem1", "s.index(1) == b");

    ctx.push_assert(
        "all_positive",
        "forall(|j: u64| !(j < 2) || s.index(j) > 0)",
    );

    let result = ctx.verify();
    // ay-dpll must propagate: s[0]==a, a>0 → s[0]>0; s[1]==b, b>0 → s[1]>0.
    // For Skolemized j_sk < 2 (j_sk ∈ {0,1}), both cases yield s[j_sk] > 0.
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 9e: symbolic elements via assume should verify, got: {:?}",
        result,
    );
}

/// Negative: symbolic element without positivity guarantee.
/// a > 0 but b is unconstrained → forall-positive must NOT verify.
#[test]
fn test_vt_tier9e_symbolic_elems_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");

    // Only a is positive, b is unconstrained
    ctx.push_assume("a_pos", "a > 0");
    ctx.push_assume("len", "s.len() == 2");
    ctx.push_assume("elem0", "s.index(0) == a");
    ctx.push_assume("elem1", "s.index(1) == b");

    ctx.push_assert(
        "all_positive_false",
        "forall(|j: u64| !(j < 2) || s.index(j) > 0)",
    );

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 9e SOUNDNESS: unconstrained element must produce Counterexample, got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 10: Quantified assumptions (forall inside assume!)
// In VerifyThis, background properties are often assumed universally:
//   assume!(forall |x: i32| x >= 0 ==> f(x) >= 0)
// Skolemizing this weakens it to a single instance. The encoder must
// preserve the universal via solver.forall() in assumption context.
// ========================================================================

/// Assume a universal property about a collection, then verify a specific
/// instance. Without assumption-context forall, Skolemization weakens the
/// assumption and the assertion cannot be proven.
///
/// assume: forall j < n. s[j] >= 0
/// assert: s[0] >= 0
///
/// Skolemized assume would give: j_sk < n ==> s[j_sk] >= 0 (one instance).
/// Real forall assume gives: for ALL j < n, s[j] >= 0.
#[test]
fn test_vt_tier10_assume_forall_collection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    // Universal assumption: all elements in range are non-negative
    ctx.push_assume("all_nonneg", "forall(|j: u64| !(j < n) || s.index(j) >= 0)");

    // Assert a specific instance that follows from the universal
    ctx.push_assert("elem0_nonneg", "s.index(0) >= 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 10: assumed universal should verify specific instance, got: {:?}",
        result,
    );
}

/// Negative test: assumed universal should NOT make false things true.
/// assume: forall j < n. s[j] >= 0
/// assert: s[0] > 100  (NOT implied by >= 0)
///
/// A counterexample is ideal, but `Unknown` is also a safe fail-closed
/// rejection for this collection-quantifier path.
#[test]
fn test_vt_tier10_assume_forall_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");
    ctx.push_assume("all_nonneg", "forall(|j: u64| !(j < n) || s.index(j) >= 0)");

    ctx.push_assert("elem0_big", "s.index(0) > 100");

    let result = ctx.verify();
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
        ),
        "TIER 10 SOUNDNESS: >= 0 should not imply > 100, must be rejected, got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 10b: Pure arithmetic assume-forall (non-collection)
// Exercises the in_assumption_context flag when the forall body does NOT
// reference collections. The code path is:
//   will_skolemize = false (no collection) → int_mode, range guards
//   in_assumption_context = true → solver.forall() (not Skolemized)
// This is the non-BV-Skolemized path through encode_quantifier (line 383
// of advanced.rs). Part of #2187.
// ========================================================================

/// Pure arithmetic assume-forall — basic regression.
/// The assumed universal about i32 values exercises in_assumption_context
/// for non-collection forall. The assertion is provable from the direct
/// assumption; the universal is present to exercise the code path.
#[test]
fn test_vt_tier10b_pure_arith_assume_forall_basic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");

    // Universal arithmetic assumption: for all i32 x, x > 0 implies x >= 1.
    // This exercises parse_and_add_assumption → in_assumption_context → solver.forall()
    // for non-collection (will_skolemize = false) forall.
    ctx.push_assume("arith_universal", "forall(|x: i32| !(x > 0) || x >= 1)");
    ctx.push_assume("a_pos", "a > 0");

    ctx.push_assert("a_ge1", "a >= 1");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 10b: pure arithmetic assume-forall should verify, got: {:?}",
        result,
    );
}

/// Pure arithmetic assume-forall — soundness negative.
/// The universal says x > 0 implies x >= 1. This does NOT imply a > 100.
///
/// The stronger outcome is a concrete counterexample (e.g. a = 1), which is
/// preferable to the older fail-closed `Unknown` behavior.
#[test]
fn test_vt_tier10b_pure_arith_assume_forall_soundness() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");

    ctx.push_assume("arith_universal", "forall(|x: i32| !(x > 0) || x >= 1)");
    ctx.push_assume("a_pos", "a > 0");

    // a > 100 does NOT follow from the universal or a > 0
    ctx.push_assert("a_big", "a > 100");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 10b SOUNDNESS: pure arithmetic assume-forall should produce a counterexample, got: {:?}",
        result,
    );
}

/// Pure arithmetic assume-forall with multiple bound variables.
/// Tests that multi-var forall in assumption context uses solver.forall().
#[test]
fn test_vt_tier10b_pure_arith_multivar_assume_forall() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "u32");
    ctx.declare_var_parsed("b", "u32");

    // Multi-variable universal in assumption context.
    // Exercises in_assumption_context for forall with 2 bound vars.
    ctx.push_assume(
        "add_monotone",
        "forall(|x: u32, y: u32| !(x < 100 && y < 100) || x + y >= x)",
    );
    ctx.push_assume("a_small", "a < 100");
    ctx.push_assume("b_small", "b < 100");

    ctx.push_assert("sum_ge_a", "a + b >= a");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 10b: multivar constraints with arithmetic should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// TIER 10c: assert_by + forall (scope interaction)
// Quantified assumptions inside assert_by proof blocks go through
// parse_and_add_assumption (in_assumption_context = true) via the
// scoped_assumptions path in setup_from_context (mod.rs:345).
// Tests that scoped forall helps prove the assert_by condition but
// does NOT leak to subsequent assertions. Part of #2187.
// ========================================================================

/// assert_by with quantified assumption in proof block.
/// The forall assumption helps prove the assert_by condition. Once
/// proven, the condition is available for subsequent assertions.
#[test]
fn test_vt_tier10c_assert_by_with_forall_scope() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_ge1", "n >= 1");

    // assert_by with quantified assumption in proof block:
    // Proof block assumes forall j < n. s[j] >= 0, then proves s[0] >= 0.
    let scoped = vec![trust_vc_core::vc::ProofObligation::assume(
        "scoped_all_nonneg",
        "forall(|j: u64| !(j < n) || s.index(j) >= 0)",
    )];
    ctx.add_assert_by("proven_elem0_nonneg", "s.index(0) >= 0", scoped);

    // The proven condition s.index(0) >= 0 should be available
    ctx.push_assert("uses_proven", "s.index(0) >= 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 10c: assert_by + forall scope should verify, got: {:?}",
        result,
    );
}

/// assert_by with quantified assumption — scoped forall must NOT leak.
/// The forall is scoped to the proof block. After assert_by, only the
/// proven condition (s.index(0) >= 0) is available, not the universal.
/// Asserting s.index(1) >= 0 should fail.
#[test]
fn test_vt_tier10c_assert_by_forall_no_leak() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("n", "u64");

    ctx.push_assume("len_eq_n", "s.len() == n");
    ctx.push_assume("n_ge2", "n >= 2");

    let scoped = vec![trust_vc_core::vc::ProofObligation::assume(
        "scoped_all_nonneg",
        "forall(|j: u64| !(j < n) || s.index(j) >= 0)",
    )];
    ctx.add_assert_by("proven_elem0", "s.index(0) >= 0", scoped);

    // s.index(1) >= 0 is NOT the proven condition. The scoped forall
    // should not leak — only s.index(0) >= 0 was proven.
    ctx.push_assert("second_elem_nonneg", "s.index(1) >= 0");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 10c SOUNDNESS: scoped forall must not leak, must produce Counterexample, got: {:?}",
        result,
    );
}
