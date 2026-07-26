//! Tests for whole-harness verification with `assert_one_fails` semantics.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::vc::{ProofObligation, SolverMode, VerificationContext};

/// Builds a `by(bit_vector)` obligation: a plain `Assert` carrying the
/// bit-vector solver mode, which is exactly how upstream `assert(...)
/// by(bit_vector)` is represented in trust-vc.
fn bv_assert(name: &str, condition: &str) -> ProofObligation {
    ProofObligation::assert(name, condition).with_solver_mode(SolverMode::BitVector)
}

/// Builds a single-proof-fn harness over one `i32` variable `x`, with the
/// supplied named assert conditions pushed in order.
fn harness_over_x(asserts: &[(&str, &str)]) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    for (name, condition) in asserts {
        ctx.push_obligation(ProofObligation::assert(*name, *condition));
    }
    ctx
}

/// Builds a single-proof-fn harness over one `u32` variable `b`, with the
/// supplied named `by(bit_vector)` conditions pushed in order.
///
/// This models the upstream `by(bit_vector)` bundles in `bitvector.rs`, where a
/// single proof fn emits several bit-vector goals and `assert_fails(err, N)`
/// localizes exactly `N` of them as counterexamples.
fn bv_harness_over_b(asserts: &[(&str, &str)]) -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("b", "u32");
    for (name, condition) in asserts {
        ctx.push_obligation(bv_assert(name, condition));
    }
    ctx
}

#[test]
fn all_assertions_verify_reports_all_verified() {
    // A harness whose every assertion is valid — the should-verify direction.
    let ctx = harness_over_x(&[
        ("a", "x + 0 == x"),
        ("b", "x * 1 == x"),
        ("c", "x - x == 0"),
    ]);

    let outcome = ctx.verify_harness();
    assert!(
        outcome.all_verified(),
        "expected AllVerified, got: {:?}",
        outcome
    );
    assert_eq!(outcome.failure_count(), 0);
    assert!(!outcome.asserts_one_fails());
    match outcome {
        HarnessOutcome::AllVerified { assertions } => assert_eq!(assertions, 3),
        other => panic!("expected AllVerified, got {other:?}"),
    }
}

#[test]
fn exactly_one_assertion_fails_reports_one_failed() {
    // Faithful `assert_one_fails`: many passing assertions and exactly one
    // counterexample, reported as a single case — the should-fail direction.
    let ctx = harness_over_x(&[
        ("a_ok", "x + 0 == x"),
        ("b_ok", "x * 1 == x"),
        ("c_fails", "x != x"), // unsatisfiable as a goal — always a counterexample
        ("d_ok", "x - x == 0"),
    ]);

    let outcome = ctx.verify_harness();
    assert!(
        outcome.asserts_one_fails(),
        "expected OneFailed (assert_one_fails), got: {:?}",
        outcome
    );
    assert!(outcome.asserts_n_fail(1));
    assert_eq!(outcome.failure_count(), 1);
    match outcome {
        HarnessOutcome::OneFailed {
            failure,
            assertions,
        } => {
            assert_eq!(assertions, 4);
            assert_eq!(
                failure.index, 2,
                "the third assertion is the one that fails"
            );
            assert_eq!(failure.name, "c_fails");
            assert!(failure.is_counterexample());
        }
        other => panic!("expected OneFailed, got {other:?}"),
    }
}

#[test]
fn one_failure_does_not_mask_a_later_failure() {
    // Two distinct assertions fail: the harness must report MultipleFailed, not
    // OneFailed. This guards the soundness property that a failed assertion is
    // never assumed for later steps and never collapses the failure count.
    let ctx = harness_over_x(&[
        ("a_ok", "x + 0 == x"),
        ("b_fails", "x != x"),
        ("c_fails", "x + 1 == x"),
    ]);

    let outcome = ctx.verify_harness();
    assert!(
        !outcome.asserts_one_fails(),
        "two failures must not be reported as assert_one_fails: {:?}",
        outcome
    );
    assert!(outcome.asserts_n_fail(2));
    assert_eq!(outcome.failure_count(), 2);
    match outcome {
        HarnessOutcome::MultipleFailed {
            failures,
            assertions,
        } => {
            assert_eq!(assertions, 3);
            assert_eq!(failures.len(), 2);
            assert_eq!(failures[0].name, "b_fails");
            assert_eq!(failures[1].name, "c_fails");
        }
        other => panic!("expected MultipleFailed, got {other:?}"),
    }
}

#[test]
fn preconditions_are_shared_by_every_assertion() {
    // Non-assertion background (here a precondition assumption) is available to
    // every assertion in the harness. Under `x > 0`, both goals hold, so the
    // whole harness verifies as a single case.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("nonneg", "x >= 0"));
    ctx.push_obligation(ProofObligation::assert("nonzero", "x != 0"));

    let outcome = ctx.verify_harness();
    assert!(
        outcome.all_verified(),
        "expected AllVerified under shared precondition, got: {:?}",
        outcome
    );
    match outcome {
        HarnessOutcome::AllVerified { assertions } => assert_eq!(assertions, 2),
        other => panic!("expected AllVerified, got {other:?}"),
    }
}

#[test]
fn earlier_proven_assertion_is_assumed_by_later_assertion() {
    // Sequential accumulation: the second assertion is only provable if the
    // first (`x >= 5`) is carried forward as a proven fact. Under `x > 10` both
    // hold, and the harness verifies — exercising the proven-fact accumulation
    // path soundly (only verified facts are assumed).
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.push_obligation(ProofObligation::assume("big", "x > 10"));
    ctx.push_obligation(ProofObligation::assert("ge_five", "x >= 5"));
    ctx.push_obligation(ProofObligation::assert("ge_one", "x >= 1"));

    let outcome = ctx.verify_harness();
    assert!(
        outcome.all_verified(),
        "expected AllVerified with accumulated facts, got: {:?}",
        outcome
    );
}

#[test]
fn outcome_predicates_are_consistent() {
    let all = HarnessOutcome::AllVerified { assertions: 3 };
    assert!(all.all_verified());
    assert!(!all.asserts_one_fails());
    assert!(!all.is_inconclusive());
    assert!(all.asserts_n_fail(0));
    assert_eq!(all.failure_count(), 0);

    let one = HarnessOutcome::OneFailed {
        failure: HarnessAssertion {
            index: 1,
            name: "f".to_string(),
            location: None,
            result: VerifyResult::Counterexample {
                obligation_name: "f".to_string(),
                model: None,
                bindings: Vec::new(),
            },
        },
        assertions: 4,
    };
    assert!(one.asserts_one_fails());
    assert!(one.asserts_n_fail(1));
    assert!(!one.all_verified());
    assert_eq!(one.failure_count(), 1);
}

#[test]
fn bit_vector_bundle_all_verify_matches_assert_fails_zero() {
    // Should-verify direction for a `by(bit_vector)` bundle: K=3 `AssertBy`
    // obligations that all hold. Faithful to upstream `... => Ok(())` cases like
    // `test1`/`test3` in bitvector.rs, where every `by(bit_vector)` assert
    // verifies. The whole case is one bundle, not three fragments.
    let ctx = bv_harness_over_b(&[
        ("and_self", "b & b == b"),      // b & b == b
        ("or_self", "b | b == b"),       // b | b == b
        ("xor_self_zero", "b ^ b == 0"), // b ^ b == 0
    ]);

    let outcome = ctx.verify_harness();
    assert!(
        outcome.all_verified(),
        "expected AllVerified for an all-passing bit_vector bundle, got: {:?}",
        outcome
    );
    assert_eq!(outcome.total_assertions(), 3, "bundle size K must be 3");
    assert_eq!(outcome.failure_count(), 0, "N must be 0");
    assert_eq!(outcome.verified_count(), 3, "K - N must be 3");
    assert!(outcome.matches_assert_fails(3, 0));
    // A bundle with these counts must NOT masquerade as any non-zero fail count.
    assert!(!outcome.matches_assert_fails(3, 1));
    assert!(
        !outcome.matches_assert_fails(2, 0),
        "wrong K must not match"
    );
}

#[test]
fn bit_vector_bundle_localizes_exactly_n_failures() {
    // Should-fail direction: K=4 `by(bit_vector)` obligations, exactly N=2 of
    // which are counterexamples and K-N=2 verified. This is the whole-case
    // `assert_fails(err, 2)` shape — the runner must see exactly two localized
    // counterexamples and two verified, in one bundle.
    let ctx = bv_harness_over_b(&[
        ("ok_and", "b & b == b"),  // verifies
        ("bad_gt", "b | b > b"),   // FAILS (b|b == b, never strictly greater)
        ("ok_xor", "b ^ b == 0"),  // verifies
        ("bad_add", "b + 1 == b"), // FAILS (no fixpoint)
    ]);

    let outcome = ctx.verify_harness();
    assert!(
        outcome.matches_assert_fails(4, 2),
        "expected exactly 2 of 4 bit_vector obligations to fail, got: {:?}",
        outcome
    );
    assert_eq!(outcome.total_assertions(), 4, "bundle size K must be 4");
    assert_eq!(outcome.failure_count(), 2, "N must be 2");
    assert_eq!(outcome.verified_count(), 2, "K - N must be 2");
    // The bundle must not satisfy a wrong fail count or wrong K.
    assert!(!outcome.matches_assert_fails(4, 1));
    assert!(!outcome.matches_assert_fails(4, 3));
    assert!(!outcome.matches_assert_fails(3, 2));
    // Faithful localization: the two failures are the marked obligations.
    match outcome {
        HarnessOutcome::MultipleFailed { failures, .. } => {
            let names: Vec<&str> = failures.iter().map(|f| f.name.as_str()).collect();
            assert_eq!(names, vec!["bad_gt", "bad_add"]);
            assert!(failures.iter().all(|f| f.is_counterexample()));
        }
        other => panic!("expected MultipleFailed, got {other:?}"),
    }
}

#[test]
fn single_bit_vector_failure_is_discharged_not_assumed() {
    // SOUNDNESS REGRESSION GUARD. A `by(bit_vector)` goal must be *discharged*
    // as an assertion, never folded into the background where it would be
    // assumed. Were it assumed, this should-fail bundle would pass as
    // `AllVerified { assertions: 0 }` — a gate-breaking false pass.
    let ctx = bv_harness_over_b(&[("bad_gt", "b | b > b")]); // FAILS

    let outcome = ctx.verify_harness();
    assert!(
        !outcome.all_verified(),
        "a failing bit_vector goal must NOT pass as AllVerified (would be unsound): {:?}",
        outcome
    );
    assert!(
        outcome.asserts_one_fails(),
        "expected OneFailed for the single failing bit_vector goal, got: {:?}",
        outcome
    );
    assert_eq!(
        outcome.total_assertions(),
        1,
        "the AssertBy goal must be counted"
    );
    assert!(outcome.matches_assert_fails(1, 1));
    assert!(!outcome.matches_assert_fails(1, 0));
}

#[test]
fn mixed_bit_vector_and_plain_assert_bundle_is_one_case() {
    // Mixed bundle: a `by(bit_vector)` goal and a plain `assert(...)` of the
    // same fact are localized together as a single whole case. This is the
    // common bitvector.rs shape (a `by(bit_vector)` assert immediately followed
    // by a plain `assert` re-stating it). Both count toward the bundle size K.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("b", "u32");
    ctx.push_obligation(bv_assert("bv_and", "b & b == b"));
    ctx.push_obligation(ProofObligation::assert("plain_and", "b & b == b"));
    ctx.push_obligation(bv_assert("bv_bad", "b + 1 == b")); // FAILS

    let outcome = ctx.verify_harness();
    assert_eq!(
        outcome.total_assertions(),
        3,
        "bit_vector and plain Assert goals both count toward the bundle size K"
    );
    assert!(
        outcome.matches_assert_fails(3, 1),
        "expected exactly 1 of 3 mixed obligations to fail, got: {:?}",
        outcome
    );
    assert_eq!(outcome.verified_count(), 2);
}
