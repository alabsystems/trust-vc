// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression: a unit (nullary) enum-variant constructor with a tester
//! postcondition must verify.
//!
//! After the native-`Sort::Datatype` migration (commit 0737e64), a nullary
//! constructor is a bare carrier-sorted constant rather than a constructor
//! *application*. ay's native datatype theory resolves `is-{ctor}` on a
//! constructor leaf only in its eager case-split pipeline, which runs solely at
//! solver scope-depth 0; trust-vc discharges every obligation inside a `push`
//! scope (depth 1). So a postcondition like `result.is_Left()` over
//! `result == Direction::Left` degraded to Unknown(Incompleteness). The fix
//! (`finish_regular_assertion_step` concrete-compute recovery) substitutes the
//! in-scope equality bindings and evaluates the tester on the concrete value,
//! upgrading the Unknown to Verified — and only ever to Verified, so a wrong
//! postcondition can never be falsely accepted.

use trust_vc_core::{extract_verification_conditions_with_file_context, VerifyResult};

fn verify(src: &str, fname: &str) -> VerifyResult {
    let file = syn::parse_file(src).expect("source should parse");
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(f) if f.sig.ident == fname => Some(f),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{fname} should exist"));
    extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{fname} should extract: {err}"))
        .verify()
}

/// The real regression: a unit-variant constructor with positive and negated
/// tester postconditions verifies.
#[test]
fn unit_variant_tester_postcondition_verifies() {
    let src = r#"
enum Direction { Left, Right }

#[trust_vc::ensures(result.is_Left())]
#[trust_vc::ensures(!result.is_Right())]
fn make_left() -> Direction { Direction::Left }
"#;
    assert!(
        matches!(verify(src, "make_left"), VerifyResult::Verified),
        "unit-variant tester postcondition should verify"
    );
}

/// Soundness guard: a WRONG tester postcondition on a unit variant must NOT be
/// accepted. The concrete-compute recovery only ever upgrades Unknown ->
/// Verified, never manufactures a false pass, so this stays non-Verified.
#[test]
fn unit_variant_wrong_tester_postcondition_is_not_verified() {
    let src = r#"
enum Direction { Left, Right }

#[trust_vc::ensures(result.is_Right())]
fn make_left_but_claim_right() -> Direction { Direction::Left }
"#;
    let result = verify(src, "make_left_but_claim_right");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a wrong unit-variant tester postcondition must never verify, got {result:?}"
    );
}

/// Soundness guard: a wrong NEGATED tester postcondition on a unit variant must
/// not be accepted either.
#[test]
fn unit_variant_wrong_negated_tester_postcondition_is_not_verified() {
    let src = r#"
enum Direction { Left, Right }

#[trust_vc::ensures(!result.is_Left())]
fn make_left_but_deny_left() -> Direction { Direction::Left }
"#;
    let result = verify(src, "make_left_but_deny_left");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a wrong negated unit-variant tester postcondition must never verify, got {result:?}"
    );
}

/// A three-variant enum where the returned unit variant is neither of the other
/// two: positive tester plus both negated testers verify.
#[test]
fn unit_variant_among_three_verifies() {
    let src = r#"
enum Color { Red, Green, Blue }

#[trust_vc::ensures(result.is_Green())]
#[trust_vc::ensures(!result.is_Red())]
#[trust_vc::ensures(!result.is_Blue())]
fn make_green() -> Color { Color::Green }
"#;
    assert!(
        matches!(verify(src, "make_green"), VerifyResult::Verified),
        "unit variant among three should verify all testers"
    );
}

/// ADVERSARIAL (added by audit): a SYMBOLIC datatype parameter whose postcondition
/// is NOT determined must never be falsely upgraded to Verified. `result == d`
/// where `d` is a symbolic `Direction` leaves `d.is_Left()` non-concrete, so the
/// concrete-compute recovery's `try_compute_eval` returns `None` (no upgrade).
/// This is the key guard that the Unknown→Verified recovery only fires on values
/// the in-scope equalities fully determine — never on symbolic inputs.
#[test]
fn symbolic_variant_param_unprovable_postcondition_is_not_verified() {
    let src = r#"
enum Direction { Left, Right }
#[trust_vc::ensures(result.is_Left())]
fn passthrough(d: Direction) -> Direction { d }
"#;
    let result = verify(src, "passthrough");
    assert!(
        !matches!(result, VerifyResult::Verified),
        "a symbolic Direction passed through must NOT verify is_Left() (it could be Right), got: {result:?}"
    );
}
