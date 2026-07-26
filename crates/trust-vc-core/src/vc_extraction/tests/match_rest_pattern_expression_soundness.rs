// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness gate for a TRAILING `..` rest in a tuple / tuple-struct pattern in
//! MATCH-EXPRESSION position (Phase E match sub-lane):
//! `match x { MatchQuad(first, ..) => <body> }` and
//! `match (a, b, c) { (f, ..) => <body> }`.
//!
//! A trailing rest lowers to `MatchPattern::Constructor { .., has_rest: true }`
//! (mirroring the already-sound `MatchPattern::Struct { has_rest }`): the N
//! LEADING bindings project to the first N field selectors (`MatchQuad_0..` /
//! `Tuple_0..`) and the remaining fields are IGNORED (no binder, no havoc, no
//! invented value). The pattern tester is unchanged — a single-variant
//! tuple/tuple-struct is TOTAL, so the arm stays irrefutable/exhaustive.
//!
//! Crux this pins — the leading binding projects to its EXACT field, and the
//! ignored fields carry no constraint:
//! * POSITIVE — `MatchQuad(first, ..) => first` verifies against `result == <the
//!   field-0 value>`, and `(f, ..) => f` likewise. Multi-leading `(a, b, ..) =>
//!   b` projects `b` to field 1.
//! * FALSE-PAYLOAD — the leading binding tied to the WRONG field's value is a
//!   counterexample: `first` is field 0, never field 1/2/3 and never an
//!   unconstrained stand-in.
//! * IGNORED-FIELD — a claim that the result equals an IGNORED (rest) field's
//!   value is not provable (that field is unbound) — a counterexample.
//! * STAY-CLOSED — a MIDDLE/back rest (`(a, .., z)` / `MatchQuad(a, .., z)`, a
//!   binding AFTER `..`) is NOT admitted this increment; it fails closed with an
//!   `unsupported pattern` diagnostic (only a trailing rest is supported).

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

// Named oracles (explicit `match`, no `matches!` on `VerifyResult`) so the
// `result_oracles::test_targeted_verification_tests_use_named_oracles` meta-test
// stays satisfied even if this file is discovered.
#[track_caller]
fn expect_verified(code: &str, func: &str) {
    match verdict(code, func) {
        VerifyResult::Verified => {}
        other => panic!("fn {func} should verify, got {other:?}"),
    }
}

#[track_caller]
fn expect_counterexample(code: &str, func: &str) {
    match verdict(code, func) {
        VerifyResult::Counterexample { .. } => {}
        other => panic!("fn {func} should produce a counterexample, got {other:?}"),
    }
}

#[track_caller]
fn expect_error_containing(code: &str, func: &str, fragment: &str) {
    match verdict(code, func) {
        VerifyResult::Error { message } => assert!(
            message.contains(fragment),
            "fn {func} should fail closed containing {fragment:?}, got: {message}"
        ),
        other => {
            panic!("fn {func} should fail closed with Error containing {fragment:?}, got {other:?}")
        }
    }
}

const QUAD: &str = "struct Quad(u64, u64, u64, u64);";

// ===========================================================================
// POSITIVE — a trailing-rest arm lowers and its value body verifies.
// ===========================================================================

#[test]
fn tuple_struct_trailing_rest_first_field_verifies() {
    // `MatchQuad(first, ..) => first` binds only field 0; result == field-0 value.
    expect_verified(
        &format!(
            r#"
            {QUAD}
            #[trust_vc::ensures(result == 10u64)]
            fn f() -> u64 {{ match Quad(10u64, 20u64, 30u64, 40u64) {{ Quad(first, ..) => first }} }}
            "#
        ),
        "f",
    );
}

#[test]
fn tuple_trailing_rest_first_field_verifies() {
    // `(f, ..) => f` over a 4-tuple binds only field 0.
    expect_verified(
        r#"
        #[trust_vc::ensures(result == 10u64)]
        fn f() -> u64 { match (10u64, 20u64, 30u64, 40u64) { (f, ..) => f } }
        "#,
        "f",
    );
}

#[test]
fn tuple_struct_two_leading_second_field_verifies() {
    // Two leading bindings: `b` must project to field 1 (distinct from field 0),
    // the trailing fields 2/3 ignored.
    expect_verified(
        &format!(
            r#"
            {QUAD}
            #[trust_vc::ensures(result == 20u64)]
            fn f() -> u64 {{ match Quad(10u64, 20u64, 30u64, 40u64) {{ Quad(a, b, ..) => b }} }}
            "#
        ),
        "f",
    );
}

#[test]
fn tuple_two_leading_second_field_verifies() {
    expect_verified(
        r#"
        #[trust_vc::ensures(result == 20u64)]
        fn f() -> u64 { match (10u64, 20u64, 30u64, 40u64) { (a, b, ..) => b } }
        "#,
        "f",
    );
}

// ===========================================================================
// FALSE-PAYLOAD — the leading binding is the EXACT field projection, not havoc.
// ===========================================================================

#[test]
fn tuple_struct_first_field_wrong_value_counterexamples() {
    // THE CRUX: body returns `first` (== field 0 == 10) against `result == 20`
    // (field 1). A counterexample proves `first` is the field-0 projection, not
    // havoc (which could not be refuted against 20) and not field 1.
    expect_counterexample(
        &format!(
            r#"
            {QUAD}
            #[trust_vc::ensures(result == 20u64)]
            fn f() -> u64 {{ match Quad(10u64, 20u64, 30u64, 40u64) {{ Quad(first, ..) => first }} }}
            "#
        ),
        "f",
    );
}

#[test]
fn tuple_first_field_wrong_value_counterexamples() {
    expect_counterexample(
        r#"
        #[trust_vc::ensures(result == 20u64)]
        fn f() -> u64 { match (10u64, 20u64, 30u64, 40u64) { (f, ..) => f } }
        "#,
        "f",
    );
}

#[test]
fn tuple_struct_second_leading_wrong_value_counterexamples() {
    // `b` is field 1 (== 20); claiming it equals field 0's value (10) refutes.
    expect_counterexample(
        &format!(
            r#"
            {QUAD}
            #[trust_vc::ensures(result == 10u64)]
            fn f() -> u64 {{ match Quad(10u64, 20u64, 30u64, 40u64) {{ Quad(a, b, ..) => b }} }}
            "#
        ),
        "f",
    );
}

// ===========================================================================
// IGNORED-FIELD — a claim that the result equals an IGNORED (rest) field's
// value is NOT provable (the rest fields are unbound / uncarried).
// ===========================================================================

#[test]
fn tuple_struct_ignored_field_value_not_provable_counterexamples() {
    // `first` == field 0 == 10; `result == 30` names field 2 (an IGNORED rest
    // field). Unprovable — the rest fields carry no constraint on the binding.
    expect_counterexample(
        &format!(
            r#"
            {QUAD}
            #[trust_vc::ensures(result == 30u64)]
            fn f() -> u64 {{ match Quad(10u64, 20u64, 30u64, 40u64) {{ Quad(first, ..) => first }} }}
            "#
        ),
        "f",
    );
}

#[test]
fn tuple_ignored_field_value_not_provable_counterexamples() {
    expect_counterexample(
        r#"
        #[trust_vc::ensures(result == 40u64)]
        fn f() -> u64 { match (10u64, 20u64, 30u64, 40u64) { (f, ..) => f } }
        "#,
        "f",
    );
}

// ===========================================================================
// STAY-CLOSED — a MIDDLE/back rest (binding AFTER `..`) is NOT admitted this
// increment; it fails closed. Only a TRAILING rest is supported.
// ===========================================================================

#[test]
fn tuple_struct_back_rest_binding_stays_fail_closed() {
    // `MatchQuad(a, .., z)` — a binding after `..` needs a field-index remap that
    // is out of scope, so it must fail closed rather than mis-bind `z`.
    expect_error_containing(
        &format!(
            r#"
            {QUAD}
            #[trust_vc::ensures(result == 10u64)]
            fn f() -> u64 {{ match Quad(10u64, 20u64, 30u64, 40u64) {{ Quad(a, .., z) => a }} }}
            "#
        ),
        "f",
        "unsupported pattern",
    );
}

#[test]
fn tuple_back_rest_binding_stays_fail_closed() {
    expect_error_containing(
        r#"
        #[trust_vc::ensures(result == 10u64)]
        fn f() -> u64 { match (10u64, 20u64, 30u64, 40u64) { (a, .., z) => a } }
        "#,
        "f",
        "unsupported pattern",
    );
}
