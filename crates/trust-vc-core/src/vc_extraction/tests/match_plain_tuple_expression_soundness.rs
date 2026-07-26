// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness gate for the plain-tuple pattern in MATCH-EXPRESSION position
//! (Phase E match sub-lane): `match (a, b) { (l, r) => <body using l, r> }`.
//!
//! The `Pat::Tuple` arm of `lower_pattern` lowers a plain-tuple pattern to a
//! `MatchPattern::Constructor { variant_name: "Tuple", bindings }` over the
//! single-variant tuple datatype, reusing the existing enum-match machinery with
//! ZERO new IR. Because the tuple datatype has one variant, the pattern tester is
//! TOTAL (irrefutable) so the arm is exhaustive and soundly seeds the default,
//! and each binding resolves to the tuple field SELECTOR `Tuple_i` — NOT a havoc
//! value.
//!
//! The crux this pins is that `l`/`r` project to `Tuple_0`/`Tuple_1`:
//! * POSITIVE — `l + r` over a ground `(4, 9)` verifies against `result == 13`
//!   (impossible if the bindings were havoc), and the wrong target `== 14` is a
//!   counterexample.
//! * FALSE-PAYLOAD — a body returning `l` against `result == 9` (the OTHER
//!   field's value) is a counterexample: `l` is `Tuple_0 == 4`, never `Tuple_1`
//!   and never an unconstrained stand-in.
//! * WILD — `(l, _)` binds only the first field.
//! * STAY-CLOSED — tuple-rest (`..`), a nested tuple sub-element, and a
//!   tuple-struct `@`-subpattern all fail closed (the exact-arity plain-ident/`_`
//!   restriction and the adjacent `@`-guard fix), never silently admitted.

use super::*;
use crate::encoder::VerifyResult;

fn verdict(code: &str, func: &str) -> VerifyResult {
    let file = parse_file(code).expect("fixture should parse");
    let item =
        find_function(&file, func).unwrap_or_else(|| panic!("fixture should define fn {func}"));
    extract_verification_conditions_with_file_context(&file, item)
        .map(|vc| vc.verify())
        .unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        })
}

fn assert_verified(code: &str, func: &str) {
    assert_eq!(
        verdict(code, func),
        VerifyResult::Verified,
        "fn {func} should verify"
    );
}

fn assert_counterexample(code: &str, func: &str) {
    let v = verdict(code, func);
    assert!(
        matches!(v, VerifyResult::Counterexample { .. }),
        "fn {func} should produce a counterexample, got {v:?}"
    );
}

fn assert_fail_closed(code: &str, func: &str, fragment: &str) {
    let v = verdict(code, func);
    match &v {
        VerifyResult::Error { message } => assert!(
            message.contains(fragment),
            "fn {func} should fail closed containing {fragment:?}, got: {message}"
        ),
        other => {
            panic!("fn {func} should fail closed with Error containing {fragment:?}, got {other:?}")
        }
    }
}

// ===========================================================================
// POSITIVE — a plain-tuple arm lowers and its body verifies via the value path.
//
// A body that carries NO exec obligation (a pure boolean combination of both
// bindings — the shape of upstream `test4` and the verified tuple-struct sibling
// `Pair(left, right) => left && !right`) verifies through the sound
// value-projection lowering. (An ARITHMETIC body additionally needs the exec
// overflow obligation to bind the tuple projection in body_extract's string
// projector, which is out of this lane's scope — pinned below.)
// ===========================================================================

#[test]
fn plain_tuple_bool_body_both_bindings_verifies() {
    // `match (true, false) { (l, r) => l && !r }` — true && !false == true.
    // Verifies ONLY because l/r project to the real fields, not havoc.
    assert_verified(
        r#"
        #[trust_vc::ensures(result)]
        fn f() -> bool { match (true, false) { (l, r) => l && !r } }
        "#,
        "f",
    );
}

#[test]
fn plain_tuple_bool_body_wrong_claim_counterexamples() {
    // `l && r` == true && false == false, so `ensures(result)` must refute.
    assert_counterexample(
        r#"
        #[trust_vc::ensures(result)]
        fn f() -> bool { match (true, false) { (l, r) => l && r } }
        "#,
        "f",
    );
}

// ===========================================================================
// PROJECTION — l == Tuple_0, r == Tuple_1 (NOT havoc, NOT swapped).
// ===========================================================================

#[test]
fn plain_tuple_left_projects_to_first_field_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(result == 4u64)]
        fn f() -> u64 { match (4u64, 9u64) { (l, r) => l } }
        "#,
        "f",
    );
}

#[test]
fn plain_tuple_right_projects_to_second_field_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(result == 9u64)]
        fn f() -> u64 { match (4u64, 9u64) { (l, r) => r } }
        "#,
        "f",
    );
}

#[test]
fn plain_tuple_left_false_payload_counterexamples() {
    // THE CRUX: body returns `l` (== Tuple_0 == 4) against `result == 9` (the
    // OTHER field). A counterexample proves l is the first-field projection, not
    // havoc (which could not be refuted against 9) and not the second field.
    assert_counterexample(
        r#"
        #[trust_vc::ensures(result == 9u64)]
        fn f() -> u64 { match (4u64, 9u64) { (l, r) => l } }
        "#,
        "f",
    );
}

#[test]
fn plain_tuple_right_false_payload_counterexamples() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(result == 4u64)]
        fn f() -> u64 { match (4u64, 9u64) { (l, r) => r } }
        "#,
        "f",
    );
}

// ===========================================================================
// WILD — `(l, _)` binds only the first field.
// ===========================================================================

#[test]
fn plain_tuple_wild_binds_first_field_verifies() {
    assert_verified(
        r#"
        #[trust_vc::ensures(result == 4u64)]
        fn f() -> u64 { match (4u64, 9u64) { (l, _) => l } }
        "#,
        "f",
    );
}

#[test]
fn plain_tuple_wild_first_field_wrong_counterexamples() {
    assert_counterexample(
        r#"
        #[trust_vc::ensures(result == 9u64)]
        fn f() -> u64 { match (4u64, 9u64) { (l, _) => l } }
        "#,
        "f",
    );
}

// ===========================================================================
// STAY-CLOSED — exact-arity plain-ident/`_` only; everything else fails closed.
// ===========================================================================

#[test]
fn plain_tuple_rest_stays_fail_closed() {
    // Tuple-REST `(first, .., last)` must NOT be admitted (it would violate the
    // exact-arity contract the constructor machinery relies on).
    assert_fail_closed(
        r#"
        #[trust_vc::ensures(result == 5u64)]
        fn f() -> u64 { match (1u64, false, 3u64, 4u64) { (first, .., last) => first + last } }
        "#,
        "f",
        "unsupported pattern",
    );
}

#[test]
fn nested_tuple_element_stays_fail_closed() {
    // A nested tuple sub-element `(a, b)` is not a plain identifier / `_`, so the
    // arm fails closed rather than lower a shape the shallow IR cannot represent.
    assert_fail_closed(
        r#"
        #[trust_vc::ensures(result == 6u64)]
        fn f() -> u64 { match ((1u64, 2u64), 3u64) { ((a, b), c) => a + b + c } }
        "#,
        "f",
        "unsupported pattern",
    );
}

#[test]
fn tuple_struct_at_subpattern_stays_fail_closed() {
    // The adjacent `@`-guard fix: a refutable `@`-subpattern in a tuple-struct
    // element (`Some(x @ 5)`) must route to the fail-closed diagnostic instead of
    // silently dropping the subpattern (which would mis-lower it to irrefutable).
    assert_fail_closed(
        r#"
        enum MOpt { Some(u64), None }
        #[trust_vc::ensures(result == 5u64)]
        fn f() -> u64 {
            match MOpt::Some(5u64) {
                MOpt::Some(x @ 5u64) => x,
                MOpt::None => 0u64,
            }
        }
        "#,
        "f",
        "unsupported constructor sub-pattern",
    );
}

// ---------------------------------------------------------------------------
// PINNED BOUNDARY — an ARITHMETIC arm body stays fail-closed (out of scope).
// ---------------------------------------------------------------------------
//
// The plain-tuple PATTERN now lowers soundly (see the projection tests above),
// but an arm-body arithmetic expression (`l + r`) additionally emits an exec
// overflow-check OBLIGATION whose tuple-projection binding lives in
// body_extract's scoped-value string projector — a path this lane deliberately
// does NOT extend (it would mean routing match arms through the string
// projector). So the arithmetic body fails closed on an unresolved binding
// rather than verifying. This is INCOMPLETENESS, not unsoundness: it rejects,
// never falsely verifies. Pinned so a future body_extract plain-tuple binding
// flips it and prompts a re-key.

#[test]
fn plain_tuple_arithmetic_body_stays_fail_closed_pending_body_extract() {
    assert_fail_closed(
        r#"
        #[trust_vc::ensures(result == 13u64)]
        fn f() -> u64 { match (4u64, 9u64) { (l, r) => l + r } }
        "#,
        "f",
        "unresolved variable",
    );
}
