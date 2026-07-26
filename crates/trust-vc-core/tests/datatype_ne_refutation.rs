// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! End-to-end coverage for the CROSS-OPERATOR datatype-disequality (`!=`)
//! soundness fix. A datatype DISEQUALITY goal over a datatype-VALUED spec-fn
//! result (`dbl(Succ(Zero)) != Succ(Succ(Zero))`, or even the tautologically-false
//! `dbl(1) != dbl(1)`) previously returned a DIRECT (wrong) `Verified`: the
//! verifier asserts the negated goal `eq(a, b)` and ay's native datatype theory
//! declares it UNSOUNDLY UNSAT at solver scope-depth 1 (constructors are only
//! case-split at depth 0). That direct `Verified` short-circuited the
//! `Incompleteness` compute refutation that already handled the `==` direction.
//!
//! The fix re-validates a CLOSED/GROUND datatype (dis)equality goal the SMT
//! reported `Verified` against the concrete evaluator (`try_compute_with_bindings`,
//! the same oracle the `==` refutation trusts); when it reduces the goal to
//! `false`, the unsound `Verified` is demoted to a Counterexample — GATED to a
//! bare goal with no constraining hypotheses.
//!
//! This is FIRST a soundness battery (the critical risk is over-rejecting a TRUE
//! `!=`):
//!   * FALSE `!=` closed/ground            -> Counterexample (was a false Verified);
//!   * TRUE  `!=` closed/ground            -> still Verified (no over-rejection);
//!   * `==` direction                      -> verdicts unchanged;
//!   * TRUE `!=` under a hypothesis        -> still Verified (gate withholds override);
//!   * never a false `Verified`, never a false Counterexample.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/datatype_ne_refutation.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn ok(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|e| panic!("extract/verify {func} failed: {e:?}"))
}

// ─────────── FALSE `!=` -> Counterexample (the closed hole) ──────────────────

/// A genuinely-false datatype `!=` (including the tautologically-false `x != x`)
/// must NOT verify — it is now a definite Counterexample, not a false `Verified`.
#[test]
fn false_datatype_disequality_is_counterexample() {
    for func in [
        "f_dbl_one_neq", // dbl(1) != Succ(Succ(Zero))   (they ARE equal)
        "f_self_neq",    // dbl(1) != dbl(1)              (tautologically false)
        "f_idn_neq",     // idn(1) != Succ(Zero)          (identity, so equal)
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Counterexample { .. }),
            "false datatype `!=` {func} must be a Counterexample, got {:?}",
            ok(func)
        );
    }
}

// ─────────── TRUE `!=` -> still Verified (no over-rejection) ─────────────────

/// The critical no-over-rejection direction: a genuinely-true datatype `!=` must
/// still Verify — the refutation must never fire on a true goal.
#[test]
fn true_datatype_disequality_still_verifies() {
    for func in [
        "t_dbl_one_neq_zero", // dbl(1) == Succ(Succ(Zero)) != Zero
        "t_idn_neq_zero",     // idn(1) == Succ(Zero)       != Zero
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Verified),
            "TRUE datatype `!=` {func} must still Verify (no over-rejection), got {:?}",
            ok(func)
        );
    }
}

// ─────────── `==` direction -> verdicts unchanged ────────────────────────────

#[test]
fn equality_direction_is_unchanged() {
    assert!(
        matches!(ok("t_dbl_one_eq"), VerifyResult::Verified),
        "TRUE datatype `==` must Verify, got {:?}",
        ok("t_dbl_one_eq")
    );
    assert!(
        matches!(
            ok("f_dbl_one_eq_wrong"),
            VerifyResult::Counterexample { .. }
        ),
        "FALSE datatype `==` must be a Counterexample, got {:?}",
        ok("f_dbl_one_eq_wrong")
    );
}

// ─────────── TRUE `!=` under a hypothesis -> still Verified ───────────────────

/// A datatype `!=` that holds because of an in-scope hypothesis must keep its
/// `Verified` verdict: the closed-ground gate withholds the refutation override
/// whenever any hypothesis is present, so the SMT `Verified` (which legitimately
/// rests on that hypothesis) is preserved — no over-rejection on the symbolic /
/// hypothesis-bearing cases.
#[test]
fn true_disequality_under_hypothesis_still_verifies() {
    for func in [
        "neq_under_eq_hyp",  // assume n == Succ(Zero); assert n != Zero
        "neq_under_neq_hyp", // assume n != Zero;        assert n != Zero
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Verified),
            "TRUE datatype `!=` under a hypothesis {func} must Verify, got {:?}",
            ok(func)
        );
    }
}
