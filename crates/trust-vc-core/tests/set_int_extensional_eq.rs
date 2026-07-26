// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! End-to-end coverage for the CONCRETE-SET extensional-equality soundness fix.
//! A direct `==` on two `Set<int>` values where the LHS is a strict SUPERSET of
//! the RHS (e.g. `{1,2} == {1}`) previously returned a false `Verified`: the
//! pointwise membership biconditional `forall e. A.contains(e) == B.contains(e)`
//! skolemizes its element, and ay's array theory fails to refute the negated goal
//! for the `Int`-indexed (`Set<int>`) membership array (validating a model where
//! the skolem read disagrees with the const-array empty base). The BV-element
//! `nat`/`i32`/`usize` variants were already sound.
//!
//! The fix specializes the equality of two CONCRETE `empty().insert(..)` chains to
//! the skolem-free two-way membership conjunction
//! `(⋀ a∈A. B.contains(a)) ∧ (⋀ b∈B. A.contains(b))` — BOTH inclusions, asserted
//! at the concrete insert keys, which the array + EUF layers decide directly.
//!
//! Soundness battery (the critical risk is the false Verified):
//!   * strict-superset / differing concrete sets -> Counterexample;
//!   * genuinely-equal concrete sets             -> still Verified (no over-rejection);
//!   * cardinality / membership controls         -> unchanged;
//!   * `nat` element variant                     -> still sound.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/set_int_extensional_eq.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn ok(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|e| panic!("extract/verify {func} failed: {e:?}"))
}

// ─────────── FALSE concrete-set equality -> Counterexample ───────────────────

/// The closed hole: a strict-superset / differing concrete `Set<int>` equality
/// must NOT verify. (`lhs_super_int` / `lhs_super_rhs2_int` were the false
/// `Verified`s; the rest were already sound and must stay refuted.)
#[test]
fn false_concrete_set_equality_is_counterexample() {
    for func in [
        "lhs_super_int",          // {1,2} == {1}   (extra element is the outer insert)
        "lhs_super3_int",         // {1,2,3} == {1}
        "lhs_super_rhs2_int",     // {1,2} == {2}   (extra element is the inner insert)
        "singleton_eq_empty_int", // {1} == {}
        "disjoint_int",           // {1} == {2}
        "rhs_super_int",          // {1} == {1,2}
        "same_card_diff_int",     // {1,2} == {1,3}
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Counterexample { .. }),
            "false concrete-set equality {func} must be a Counterexample, got {:?}",
            ok(func)
        );
    }
}

// ─────────── TRUE concrete-set equality -> still Verified ────────────────────

/// The no-over-rejection direction: a genuinely-equal concrete `Set<int>`
/// equality must still Verify, including reordered inserts and empty == empty.
#[test]
fn true_concrete_set_equality_still_verifies() {
    for func in [
        "equal_int",           // {1,2} == {1,2}
        "equal_reordered_int", // {1,2} == {2,1}
        "empty_eq_empty_int",  // {} == {}
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Verified),
            "TRUE concrete-set equality {func} must still Verify (no over-rejection), got {:?}",
            ok(func)
        );
    }
}

// ─────────── cardinality / membership controls -> unchanged ──────────────────

#[test]
fn cardinality_and_membership_controls_unchanged() {
    for func in ["len_two_int", "contains_pos_int", "not_contains_int"] {
        assert!(
            matches!(ok(func), VerifyResult::Verified),
            "control {func} must still Verify, got {:?}",
            ok(func)
        );
    }
}

// ─────────── nat element variant stays sound ─────────────────────────────────

#[test]
fn nat_element_variant_is_sound() {
    assert!(
        matches!(ok("lhs_super_nat"), VerifyResult::Counterexample { .. }),
        "{{1,2}} == {{1}} over nat must be a Counterexample, got {:?}",
        ok("lhs_super_nat")
    );
    assert!(
        matches!(ok("equal_nat"), VerifyResult::Verified),
        "{{1,2}} == {{1,2}} over nat must Verify, got {:?}",
        ok("equal_nat")
    );
}
