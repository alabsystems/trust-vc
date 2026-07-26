// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! End-to-end coverage for STRUCTURAL-DESCENT `#[decreases]` over a recursive
//! datatype: a recursive spec fn whose declared measure is a recursive-datatype
//! parameter earns its defining (recursive-unfolding) axiom ONLY when the
//! termination gate proves the matched structural child strictly shrinks
//! `dt_size`. The decrease is derived solely from (i) the match-arm constructor
//! equation lifted verbatim from the body case-split (`n == Succ(p)`) and (ii)
//! the already-trusted `dt_size` acyclicity recurrence
//! (`size(Succ(p)) == 1 + size(p)`, `size(_) >= 0`) — no new trusted assumption.
//!
//! This is FIRST a soundness battery (#50 class: a "present-but-non-decreasing"
//! `decreases` must NOT mint an unsound axiom):
//!   * TRUE structural-recursion goals verify (`depth`/`len`, base AND deeper);
//!   * FALSE goals are NEVER `Verified` (Counterexample or fail-closed Unknown);
//!   * SELF-recursion on the same parameter, NON-CHILD recursion on an unrelated
//!     parameter, and ill-founded (no terminating base) recursion all keep their
//!     defining axiom SUPPRESSED — a false fact asserted through them is never
//!     proved (the function stays an uninterpreted helper).
//!
//! Branching recursion (two self-calls, e.g. a tree size) is intentionally not
//! exercised: the gate admits its axiom soundly, but ay's e-matching diverges on
//! a doubly-self-triggering quantified axiom — an orthogonal, pre-existing solver
//! limitation, not a soundness gap.

use trust_vc_core::{verify_function_from_file, VerifyResult};

fn path() -> String {
    format!(
        "{}/tests/data/recursive_structural_decreases.rs",
        env!("CARGO_MANIFEST_DIR")
    )
}

fn ok(func: &str) -> VerifyResult {
    verify_function_from_file(&path(), func)
        .unwrap_or_else(|e| panic!("extract/verify {func} failed: {e:?}"))
}

// ───────────────────────── TRUE → Verified ─────────────────────────────────

/// Genuine structural descent on a match-bound child verifies its true goals —
/// base case AND a deeper value that requires the unfolding axiom to fire more
/// than once. Covers `Nat` (Peano) and a payload-carrying `IntList`.
#[test]
fn structural_recursion_true_goals_verify() {
    for func in [
        "t_depth_zero", // depth(Zero) == 0
        "t_depth_one",  // depth(Succ(Zero)) == 1
        "t_depth_two",  // depth(Succ(Succ(Zero))) == 2
        "t_len_zero",   // len(Nil) == 0
        "t_len_one",    // len(Cons(7, Nil)) == 1
        "t_len_two",    // len(Cons(7, Cons(8, Nil))) == 2
    ] {
        assert!(
            matches!(ok(func), VerifyResult::Verified),
            "TRUE structural-recursion goal {func} must Verify, got {:?}",
            ok(func)
        );
    }
}

// ───────────────────── FALSE → never Verified (sound) ──────────────────────

#[test]
fn false_goals_are_never_verified() {
    for func in ["f_depth_one_wrong", "f_len_one_wrong"] {
        let result = ok(func);
        assert!(
            !matches!(result, VerifyResult::Verified),
            "UNSOUND: false structural-recursion goal {func} must NOT Verify, got {result:?}"
        );
    }
}

// ─── SELF-RECURSION on the same parameter: axiom SUPPRESSED (#50 — DECISIVE) ──

/// A spec fn that recurses on its scrutinee (`Succ(p) => 1 + self_rec(n)`) is not
/// structurally decreasing (`size(n) < size(n)` is false), so its defining axiom
/// — which would be contradictory (`self_rec(Succ(p)) == 1 + self_rec(Succ(p))`)
/// — must stay SUPPRESSED. Asserting a genuine arithmetic falsehood through it
/// must therefore NEVER verify; the function stays an uninterpreted helper.
#[test]
fn self_recursion_axiom_stays_suppressed() {
    let no_false = ok("self_rec_no_false");
    assert!(
        !matches!(no_false, VerifyResult::Verified),
        "UNSOUND: self-recursion (same-parameter) must stay uninterpreted; \
         `0 == 1` must NOT verify through it, got {no_false:?}"
    );

    // The base-case fact would follow only from the suppressed defining axiom;
    // with the axiom suppressed it must stay unproven (never a false refutation
    // either, since it is true).
    let base = ok("self_rec_base_unproven");
    assert!(
        !matches!(
            base,
            VerifyResult::Verified | VerifyResult::Counterexample { .. }
        ),
        "self_rec base fact must stay unproven (uninterpreted helper), got {base:?}"
    );
}

// ─── NON-CHILD recursion: recurse on an unrelated parameter → SUPPRESSED ──────

#[test]
fn non_child_recursion_axiom_stays_suppressed() {
    let result = ok("non_child_no_false");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "UNSOUND: recursion on a non-child parameter must stay uninterpreted; \
         `0 == 1` must NOT verify through it, got {result:?}"
    );
}

// ─── NO terminating base case: ill-founded recursion → SUPPRESSED ────────────

#[test]
fn ill_founded_recursion_axiom_stays_suppressed() {
    let result = ok("no_base_no_false");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "UNSOUND: ill-founded recursion (no terminating base) must stay \
         uninterpreted; `0 == 1` must NOT verify through it, got {result:?}"
    );
}
