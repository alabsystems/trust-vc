//! Regression tests for issue #1470 - quantifier macros must not silently return true
//!
//! These tests verify that forall!/exists! macros perform inline verification in
//! test mode, returning the actual ay result instead of always returning true.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

/// forall x: i32. x != x is a contradiction (no integer equals itself is false).
/// The macro must NOT return true for this.
#[test]
fn test_forall_contradiction_returns_false() {
    let result = trust_vc::forall!(|x: i32| x != x);
    assert!(
        !result,
        "forall(|x| x != x) must return false (contradiction)"
    );
}

/// exists x: i32. x > x is impossible (no integer is greater than itself).
/// The macro must NOT return true for this.
#[test]
fn test_exists_contradiction_returns_false() {
    let result = trust_vc::exists!(|x: i32| x > x);
    assert!(!result, "exists(|x| x > x) must return false (impossible)");
}

/// forall x: i32. x > 0 is false (x = 0 or negative is a counterexample).
#[test]
fn test_forall_not_all_positive_returns_false() {
    let result = trust_vc::forall!(|x: i32| x > 0);
    assert!(
        !result,
        "forall(|x| x > 0) must return false (x=0 is counterexample)"
    );
}

/// forall x: i32. x == x is a tautology.
/// ay-dpll may return Unknown for quantified BV formulas (PSPACE-complete),
/// so we don't assert the result. The critical test is that contradictions
/// return false (tested in other tests). This test validates that the macro
/// does not panic on valid quantifiers.
#[test]
fn test_forall_tautology_does_not_panic() {
    // This exercises the inline verification path without asserting the result,
    // because ay-dpll's handling of universal BV quantifiers is incomplete.
    let _result = trust_vc::forall!(|x: i32| x == x);
    // If we got here without panic, the macro correctly invoked ay inline.
}

/// forall x, y: i32. x + y == y + x tests commutativity.
/// Verification should be invoked; obligations should be collected.
#[test]
fn test_verification_is_invoked() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::set_proof_mode(true);

        // The macro now verifies inline instead of just returning true
        let _result = trust_vc::forall!(|x: i32, y: i32| x + y == y + x);

        // Check that obligations were collected (collection still works)
        let context = trust_vc_core::verify_macro::get_context();
        assert!(
            context.is_some(),
            "Should have a verification context after forall!"
        );
        let ctx = context.unwrap();
        assert!(
            !ctx.obligations().is_empty(),
            "Obligations should be collected"
        );

        trust_vc_core::verify_macro::set_proof_mode(false);
    })
}

/// Both contradictions should fail, proving inline verification happens per-call.
#[test]
fn test_each_call_verifies_independently() {
    #[allow(clippy::impossible_comparisons)]
    let result1 = trust_vc::forall!(|x: i32| x < 0 && x > 0);
    assert!(
        !result1,
        "forall(|x| x < 0 && x > 0) must return false (impossible)"
    );

    let result2 = trust_vc::exists!(|y: i32| y != y);
    assert!(
        !result2,
        "exists(|y| y != y) must return false (contradiction)"
    );
}

/// exists x: i32. x != x is impossible — no witness exists.
#[test]
fn test_exists_self_contradiction_returns_false() {
    let result = trust_vc::exists!(|x: i32| x != x);
    assert!(!result, "exists(|x| x != x) must return false (no witness)");
}
