//! Soundness tests: an `exists`-over-`forall` (∃j.∀i) goal must NOT be proven by
//! silently swapping it into the weaker ∀i.∃j reading.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! P1-D (quantifier Skolemization polarity swap). A trigger-less assertion-
//! position `forall` was Skolemized to a free witness whenever it was NOT in an
//! assumption context — regardless of nesting. A `forall` positively nested
//! under a real `exists` therefore leaked its bound variable to the outermost
//! scope, where verification-by-refutation universally closed it, turning the
//! strong `∃j.∀i.P` into the weak `∀i.∃j.P`. Concretely `exists j. forall i.
//! i <= j` ("there is a greatest integer") is FALSE but verified.
//!
//! The fix keeps a `forall` nested under a real quantifier as a real quantifier
//! (both in the positive encoder and the refutation encoder), so the FALSE goals
//! below are NOT verified (Counterexample or Unknown), while the genuinely TRUE
//! `∀i.∃j` analogs still verify (no over-rejection).

use crate::encoder::types::VerifyResult;
use crate::encoder::AYEncoder;
use crate::vc::VerificationContext;

fn verify_goal(goal: &str) -> VerifyResult {
    let mut ctx = VerificationContext::new();
    ctx.push_assert("goal", goal);
    AYEncoder::verify(&ctx)
}

/// Soundness gate: a FALSE goal must NOT verify. Anything that is not `Verified`
/// (Counterexample / Unknown / Error) is acceptable for soundness.
fn assert_not_verified(goal: &str) {
    let result = verify_goal(goal);
    assert!(
        !matches!(result, VerifyResult::Verified),
        "FALSE goal `{goal}` must NOT verify (got {result:?})"
    );
}

/// No-over-rejection gate: a genuinely TRUE goal must still verify.
fn assert_verified(goal: &str) {
    let result = verify_goal(goal);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TRUE goal `{goal}` must verify (got {result:?})"
    );
}

// ───────────────────────── FALSE ∃j.∀i goals ─────────────────────────

#[test]
fn exists_forall_eq_is_not_verified() {
    // No integer j is equal to every integer i.
    assert_not_verified("exists |j: int| forall |i: int| i == j");
}

#[test]
fn exists_forall_le_is_not_verified() {
    // No greatest integer (no j with i <= j for all i).
    assert_not_verified("exists |j: int| forall |i: int| i <= j");
}

#[test]
fn exists_forall_lt_is_not_verified() {
    // Integers have no strict upper bound.
    assert_not_verified("exists |j: int| forall |i: int| i < j");
}

#[test]
fn exists_forall_gt_is_not_verified() {
    // Integers have no strict lower bound.
    assert_not_verified("exists |j: int| forall |i: int| i > j");
}

#[test]
fn exists_forall_nat_greatest_is_not_verified() {
    // No greatest natural number.
    assert_not_verified("exists |j: nat| forall |i: nat| (i as int) <= (j as int)");
}

#[test]
fn three_level_forall_exists_forall_is_not_verified() {
    // forall i. exists j. forall k. k < j — the inner `forall k` is false for
    // every j (take k = j), so the whole statement is false.
    assert_not_verified("forall |i: int| exists |j: int| forall |k: int| k < j");
}

// ───────────── TRUE ∀i.∃j analogs (must still verify) ─────────────

#[test]
fn forall_exists_eq_still_verifies() {
    // For every i there is a j equal to it (the consistent quantifier order).
    assert_verified("forall |i: int| exists |j: int| i == j");
}

#[test]
fn forall_exists_gt_still_verifies() {
    // For every i there is a strictly greater j (integers unbounded above).
    assert_verified("forall |i: int| exists |j: int| j > i");
}

#[test]
fn forall_exists_nat_ge_still_verifies() {
    assert_verified("forall |i: nat| exists |j: nat| (i as int) <= (j as int)");
}

#[test]
fn forall_exists_nat_le_still_verifies() {
    assert_verified("forall |i: nat| exists |j: nat| (j as int) >= (i as int)");
}

#[test]
fn strict_order_is_not_treated_as_reflexive() {
    // The constructive non-strict-order route must not instantiate `j := i`
    // for `<`; that candidate is false.
    assert_not_verified("forall |i: nat| exists |j: nat| (j as int) < (i as int)");
}

#[test]
fn bounded_endpoint_false_case_is_not_verified() {
    // A finite carrier has a maximum, so `j > i` is false at the endpoint.
    assert_not_verified("forall |i: u8| exists |j: u8| j > i");
}

#[test]
fn mismatched_candidate_type_does_not_use_reflexive_witness() {
    // The existential binder and the outer candidate have different types;
    // the constructive witness gate must fall back to the quantified path.
    assert_not_verified("forall |i: int| exists |j: nat| (j as int) <= (i as int)");
}

#[test]
fn simple_exists_still_verifies() {
    assert_verified("exists |j: int| j == 0");
}

// ───────────── Controls: top-level / universal-prefix foralls ─────────────

#[test]
fn top_level_false_forall_is_not_verified() {
    // A genuinely universal goal in goal position is still soundly refuted —
    // Skolemization of an OUTERMOST forall is correct and must be preserved.
    assert_not_verified("forall |i: int| i == 0");
}

#[test]
fn nested_false_foralls_are_not_verified() {
    // A universal prefix (forall under forall) is still soundly refuted.
    assert_not_verified("forall |a: int| forall |b: int| forall |k: int| k < 0");
}
