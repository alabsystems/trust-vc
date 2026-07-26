#![cfg(feature = "strings")]
// End-to-end tests for capability #5: exact string/byte proofs.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// These build fully-typed `DriverFn`s over `str`/`String` parameters and run
// them through trust-vc-core's REAL encoder + ay solver. They demonstrate the
// `Seq<char>` string view end to end:
//   * a true string-length relation VERIFIES,
//   * `char`-at indexing reasons over the view, and
//   * a false postcondition with a string parameter in scope is REFUTED with a
//     concrete counterexample — the seam is sound, not a rubber stamp.
//
// Where the default (non-`native-strings`) Array-backed string encoding cannot
// decide a goal, the backend returns `Unknown` rather than a false `Verified`;
// these tests stay on the decidable, load-bearing fragment (length/index logic).

use trust_vc_core::ir::{CompareOp, TrustVcType};
use trust_vc_driver::lower::{Binding, DriverFn, Outcome};
use trust_vc_driver::strings::{
    char_at, char_lit, compare, len_add, len_lit, len_nonneg, str_len, str_slice, string,
};

fn bool_result() -> Binding {
    Binding::new("result", TrustVcType::Bool)
}

// --------------------------------------------------------------------------
// VERIFIES — true facts about the `Seq<char>` string view.
// --------------------------------------------------------------------------

/// fn cmp_lens(a: &str, b: &str) -> bool
///     requires a.len() == 2, b.len() == 3
///     ensures  a.len() < b.len()
///
/// A genuine cross-string length relation, proven over the integer-typed
/// length view of two distinct symbolic strings.
#[test]
fn shorter_string_has_smaller_len_verifies() {
    let f = DriverFn {
        name: "cmp_lens".into(),
        params: vec![
            Binding::new("a", str_slice()),
            Binding::new("b", str_slice()),
        ],
        result: bool_result(),
        requires: vec![
            compare(CompareOp::Eq, str_len("a", str_slice()), len_lit(2)),
            compare(CompareOp::Eq, str_len("b", str_slice()), len_lit(3)),
        ],
        body_value: None,
        ensures: vec![compare(
            CompareOp::Lt,
            str_len("a", str_slice()),
            str_len("b", str_slice()),
        )],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// fn len_bound(s: String) -> bool
///     requires s.len() == 3
///     ensures  s.len() < 10 && s.len() >= 3
///
/// Length-fact transitivity over an owned `String` view.
#[test]
fn known_len_implies_bounds_verifies() {
    let f = DriverFn {
        name: "len_bound".into(),
        params: vec![Binding::new("s", string())],
        result: bool_result(),
        requires: vec![compare(CompareOp::Eq, str_len("s", string()), len_lit(3))],
        body_value: None,
        ensures: vec![
            compare(CompareOp::Lt, str_len("s", string()), len_lit(10)),
            compare(CompareOp::Ge, str_len("s", string()), len_lit(3)),
        ],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// fn first_char_stable(s: &str) -> bool
///     requires s.len() == 3        // bounds the index-0 access
///     ensures  s[0] == s[0]
///
/// `char`-at indexing over the `Seq<char>` view: the indexed element is a
/// first-class `char` (BitVec(32)) term that the encoder can name and relate.
/// The length precondition discharges the encoder's `0 < len` bounds check.
#[test]
fn char_at_is_reflexive_verifies() {
    let f = DriverFn {
        name: "first_char_stable".into(),
        params: vec![Binding::new("s", str_slice())],
        result: bool_result(),
        requires: vec![compare(
            CompareOp::Eq,
            str_len("s", str_slice()),
            len_lit(3),
        )],
        body_value: None,
        ensures: vec![compare(
            CompareOp::Eq,
            char_at("s", str_slice(), 0),
            char_at("s", str_slice(), 0),
        )],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

// --------------------------------------------------------------------------
// REFUTED — a false postcondition is caught with a counterexample, even with a
// string parameter (and its length view) in scope.
// --------------------------------------------------------------------------

/// fn bad_int_fact(s: &str, n: i64) -> bool
///     requires s.len() >= 0          // string view grounded but length free
///     ensures  n == n + 1            // false for every n
///
/// The string's `Seq<char>` view is in scope (and asserted non-negative), yet
/// the false integer postcondition is still refuted with a concrete
/// counterexample — the string never rubber-stamps an unsound proof.
#[test]
fn false_postcondition_refuted_with_string_in_scope() {
    let f = DriverFn {
        name: "bad_int_fact".into(),
        params: vec![
            Binding::new("s", str_slice()),
            Binding::new("n", TrustVcType::Int { width: 64 }),
        ],
        result: bool_result(),
        requires: vec![len_nonneg("s", str_slice())],
        body_value: None,
        // n == n + 1  -- unsatisfiable, so refutable with a counterexample.
        ensures: vec![compare(
            CompareOp::Eq,
            len_add(len_lit(0), n_var()),
            len_add(n_var(), len_lit(1)),
        )],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
    if let trust_vc_core::VerifyResult::Counterexample { model, .. } = &raw {
        assert!(model.is_some(), "expected a counterexample model: {raw:?}");
    }
}

/// A tightened, definitely-false length bound is refuted, with the string's
/// length view grounded by a non-binding `>= 0` assumption.
///
/// fn bad_len_bound(s: &str, n: i64) -> bool
///     requires s.len() >= 0, n == 3
///     ensures  n < 3
#[test]
fn false_len_derived_bound_refuted() {
    let f = DriverFn {
        name: "bad_len_bound".into(),
        params: vec![
            Binding::new("s", str_slice()),
            Binding::new("n", TrustVcType::Int { width: 64 }),
        ],
        result: bool_result(),
        requires: vec![
            len_nonneg("s", str_slice()),
            compare(CompareOp::Eq, n_var(), len_lit(3)),
        ],
        body_value: None,
        ensures: vec![compare(CompareOp::Lt, n_var(), len_lit(3))],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

// --------------------------------------------------------------------------
// FAIL-CLOSED — a true char-relation that the default encoding cannot decide
// must NOT come back Verified; Unknown is the acceptable conservative verdict.
// --------------------------------------------------------------------------

/// fn distinct_chars(s: &str) -> bool
///     requires s[0] == 'a'
///     ensures  s[0] != 'b'
///
/// This is *true*, but the Array-backed default string encoding cannot decide
/// it; the seam must stay sound and return a non-`Verified` verdict rather than
/// rubber-stamp it. (If a future encoder upgrade proves it, `Verified` is also
/// acceptable — the assertion below excludes only the unsound `Refuted`.)
#[test]
fn undecidable_char_fact_is_not_unsoundly_refuted() {
    let f = DriverFn {
        name: "distinct_chars".into(),
        params: vec![Binding::new("s", str_slice())],
        result: bool_result(),
        requires: vec![compare(
            CompareOp::Eq,
            char_at("s", str_slice(), 0),
            char_lit('a'),
        )],
        body_value: None,
        ensures: vec![compare(
            CompareOp::Ne,
            char_at("s", str_slice(), 0),
            char_lit('b'),
        )],
    };

    let (outcome, raw) = f.verify();
    assert_ne!(
        outcome,
        Outcome::Refuted,
        "a true char fact must never be refuted (unsound): {raw:?}"
    );
}

fn n_var() -> trust_vc_core::ir::TrustVcExpr {
    trust_vc_core::ir::TrustVcExpr::Var {
        name: "n".into(),
        ty: TrustVcType::Int { width: 64 },
    }
}
