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

/// fn cmp_lens_wrong_way(a: &str, b: &str) -> bool
///     requires a.len() == 3, b.len() == 2
///     ensures  a.len() < b.len()
///
/// The negative twin of `shorter_string_has_smaller_len_verifies`: the same
/// length-vs-length comparison (both operands Int-sorted length terms), made
/// FALSE. It must be refuted, so the pair shows the comparison is decided,
/// not rubber-stamped.
#[test]
fn longer_string_is_not_shorter_refuted() {
    let f = DriverFn {
        name: "cmp_lens_wrong_way".into(),
        params: vec![
            Binding::new("a", str_slice()),
            Binding::new("b", str_slice()),
        ],
        result: bool_result(),
        requires: vec![
            compare(CompareOp::Eq, str_len("a", str_slice()), len_lit(3)),
            compare(CompareOp::Eq, str_len("b", str_slice()), len_lit(2)),
        ],
        body_value: None,
        ensures: vec![compare(
            CompareOp::Lt,
            str_len("a", str_slice()),
            str_len("b", str_slice()),
        )],
    };

    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

/// fn below_negative(a: &str) -> bool
///     requires a.len() == 2
///     ensures  a.len() < -1        // `-1` at the view's `i64` length type
///
/// FALSE for every string. The length term is Int and the `i64` literal is a
/// BV peer, so this crosses the Int/BV comparison boundary; it must never
/// come back `Verified`.
#[test]
fn length_below_a_negative_bound_is_not_verified() {
    let f = DriverFn {
        name: "below_negative".into(),
        params: vec![Binding::new("a", str_slice())],
        result: bool_result(),
        requires: vec![compare(
            CompareOp::Eq,
            str_len("a", str_slice()),
            len_lit(2),
        )],
        body_value: None,
        ensures: vec![compare(
            CompareOp::Lt,
            str_len("a", str_slice()),
            len_lit(-1),
        )],
    };

    let (outcome, raw) = f.verify();
    assert_ne!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
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

// --------------------------------------------------------------------------
// SIGNEDNESS IS THE OPERAND'S — measured false verdicts at the Int/BV
// boundaries of a string length (trust-vc-core
// `tests/operand_signedness_soundness.rs` pins the same shapes).
// --------------------------------------------------------------------------

fn lit_of(value: i128, ty: TrustVcType) -> trust_vc_core::ir::TrustVcExpr {
    trust_vc_core::ir::TrustVcExpr::IntLit { value, ty }
}

/// requires a.len() == 0; ensures `value` (a `u8`) < a.len() + `peer` (an
/// `i8`). FALSE. `len_add` declares the node `i64`, which `i64 + i8` does not
/// derive: the IR typing validator refuses that claim (trust-vc-core §5b rule
/// 13). Declared at the exact `int` it derives, the goal is refuted.
fn u8_below_len_plus_i8(name: &str, value: i128, peer: i128) {
    let goal = |sum: fn(_, _) -> _| {
        let peer = lit_of(peer, TrustVcType::Int { width: 8 });
        let sum = sum(str_len("a", str_slice()), peer);
        compare(
            CompareOp::Lt,
            lit_of(value, TrustVcType::Uint { width: 8 }),
            sum,
        )
    };
    let lie = one_string_fn(&format!("{name}_i64"), 0, vec![], vec![], goal(len_add));
    for (outcome, raw) in [lie.verify(), lie.verify_exec()] {
        let refused = matches!(outcome, Outcome::Error(_) | Outcome::Unknown);
        assert!(refused, "{name}: a declared-type lie was decided: {raw:?}");
    }
    let exact_add = |l, r| trust_vc_core::ir::TrustVcExpr::Arith {
        op: trust_vc_core::ir::ArithOp::Add,
        left: Box::new(l),
        right: Box::new(r),
        ty: TrustVcType::MathInt,
    };
    let f = one_string_fn(name, 0, vec![], vec![], goal(exact_add));
    assert_both_modes(&f, &Outcome::Refuted);
}

fn one_string_fn(
    name: &str,
    len: i128,
    extra: Vec<Binding>,
    extra_requires: Vec<trust_vc_core::ir::TrustVcExpr>,
    ensures: trust_vc_core::ir::TrustVcExpr,
) -> DriverFn {
    let mut params = vec![Binding::new("a", str_slice())];
    params.extend(extra);
    let mut requires = vec![compare(
        CompareOp::Eq,
        str_len("a", str_slice()),
        len_lit(len),
    )];
    requires.extend(extra_requires);
    DriverFn {
        name: name.into(),
        params,
        result: bool_result(),
        requires,
        body_value: None,
        ensures: vec![ensures],
    }
}

fn assert_both_modes(f: &DriverFn, expected: &Outcome) {
    let (outcome, raw) = f.verify();
    assert_eq!(&outcome, expected, "{} verify: {raw:?}", f.name);
    let (outcome, raw) = f.verify_exec();
    assert_eq!(&outcome, expected, "{} verify_exec: {raw:?}", f.name);
}

/// requires a.len() == 0; ensures u64::MAX < a.len() + (-1i64). FALSE.
/// `u64::MAX` and `-1i64` are one hash-consed BV64 term; the comparison lifted
/// the left operand with the signedness the RIGHT operand's literal had just
/// registered for that term, and returned `Verified`.
#[test]
fn u64_max_below_len_minus_one_is_refuted() {
    let f = one_string_fn(
        "u64_max_below",
        0,
        vec![],
        vec![],
        compare(
            CompareOp::Lt,
            lit_of(i128::from(u64::MAX), TrustVcType::Uint { width: 64 }),
            len_add(str_len("a", str_slice()), len_lit(-1)),
        ),
    );
    assert_both_modes(&f, &Outcome::Refuted);
}

/// requires a.len() == 0; ensures 200u8 < a.len() + (-56i8). FALSE.
#[test]
fn two_hundred_u8_below_len_minus_56_i8_is_refuted() {
    u8_below_len_plus_i8("u8_200_below", 200, -56);
}

/// requires a.len() == 0; ensures 255u8 < a.len() + (-1i8). FALSE.
#[test]
fn two_fifty_five_u8_below_len_minus_one_i8_is_refuted() {
    u8_below_len_plus_i8("u8_255_below", 255, -1);
}

/// requires a.len() == 2; ensures a.len() + (-3) > 100. FALSE. The arithmetic
/// boundary lifted the signed peer UNSIGNED: `2 + 2^64 - 3` (`Verified`).
#[test]
fn len_plus_negative_literal_is_not_large() {
    let f = one_string_fn(
        "len_plus_neg_large",
        2,
        vec![],
        vec![],
        compare(
            CompareOp::Gt,
            len_add(str_len("a", str_slice()), len_lit(-3)),
            len_lit(100),
        ),
    );
    assert_both_modes(&f, &Outcome::Refuted);
}

/// requires a.len() == 2, n == -3; ensures a.len() + n > 100. FALSE.
#[test]
fn len_plus_negative_variable_is_not_large() {
    let f = one_string_fn(
        "len_plus_n_large",
        2,
        vec![Binding::new("n", TrustVcType::Int { width: 64 })],
        vec![compare(CompareOp::Eq, n_var(), len_lit(-3))],
        compare(
            CompareOp::Gt,
            len_add(str_len("a", str_slice()), n_var()),
            len_lit(100),
        ),
    );
    assert_both_modes(&f, &Outcome::Refuted);
}

/// requires a.len() == 2; ensures a.len() + (-3) < 0. TRUE — was refuted
/// with a false counterexample.
#[test]
fn len_plus_negative_literal_is_negative_verifies() {
    let f = one_string_fn(
        "len_plus_neg_negative",
        2,
        vec![],
        vec![],
        compare(
            CompareOp::Lt,
            len_add(str_len("a", str_slice()), len_lit(-3)),
            len_lit(0),
        ),
    );
    assert_both_modes(&f, &Outcome::Verified);
}

/// requires a.len() == 2, n == -3; ensures a.len() - n == 5. TRUE — was
/// refuted with a false counterexample.
#[test]
fn len_minus_negative_variable_is_five_verifies() {
    let f = one_string_fn(
        "len_minus_n_five",
        2,
        vec![Binding::new("n", TrustVcType::Int { width: 64 })],
        vec![compare(CompareOp::Eq, n_var(), len_lit(-3))],
        compare(
            CompareOp::Eq,
            trust_vc_core::ir::TrustVcExpr::Arith {
                op: trust_vc_core::ir::ArithOp::Sub,
                left: Box::new(str_len("a", str_slice())),
                right: Box::new(n_var()),
                ty: TrustVcType::Int { width: 64 },
            },
            len_lit(5),
        ),
    );
    assert_both_modes(&f, &Outcome::Verified);
}
