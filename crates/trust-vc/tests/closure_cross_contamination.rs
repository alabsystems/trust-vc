// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Soundness regression: cross-closure assumption contamination (#791).
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! A closure `requires(P)` in BodyLevel mode is a global hypothesis over the
//! shared `__trust_vc_closure_arg{i}` / `__trust_vc_closure_result` symbols.
//! Before the per-closure-unique-symbol fix, one closure's precondition leaked
//! into a *sibling* closure's obligations, discharging false postconditions.

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

// ── (a) Adversarial: contamination must NOT produce a false Verified ──

/// Two single-param `u64` closures. `a` has `requires(x > 100)`; `b` has a
/// *false* `ensures(res > 100)` over body `x`. If `a`'s precondition leaks to
/// `b` (shared symbols), `b` wrongly verifies. It must NOT.
#[test]
fn test_two_closure_contamination_b_must_be_counterexample() {
    let result = common::verify_and_get_result(|| {
        let a = trust_vc::closure!(
            |x: u64|
            requires(x > 100u64)
            ensures(|res: u64| res == x)
            x
        );
        let _ = a(200u64);

        let b = trust_vc::closure!(
            |x: u64|
            ensures(|res: u64| res > 100u64)
            x
        );
        let _ = b(5u64);
    });

    assert!(
        !matches!(result, VerifyResult::Verified),
        "FALSE VERIFIED: closure b's `res > 100` over body `x` must not verify; \
         a's requires(x > 100) must not leak. Got: {result:?}"
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "b's bogus postcondition should produce a counterexample, got: {result:?}"
    );
}

/// Control: closure `b` alone (no sibling `a`) is already a counterexample.
#[test]
fn test_closure_b_alone_is_counterexample() {
    let result = common::verify_and_get_result(|| {
        let b = trust_vc::closure!(
            |x: u64|
            ensures(|res: u64| res > 100u64)
            x
        );
        let _ = b(5u64);
    });
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "b alone must be a counterexample, got: {result:?}"
    );
}

/// Probe-6: after defining `a` (with requires(arg0 > 100)), a *bare* obligation
/// over the legacy unscoped symbol `__trust_vc_closure_arg0 > 100` must NOT be
/// vacuously verified by a leaked precondition.
#[test]
fn test_probe6_bare_closure_symbol_obligation_not_verified() {
    let result = common::verify_and_get_result(|| {
        let a = trust_vc::closure!(
            |x: u64|
            requires(x > 100u64)
            ensures(|res: u64| res == x)
            x
        );
        let _ = a(200u64);

        // A bare obligation over the legacy shared symbol. No closure should be
        // constraining this exact name post-fix.
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "probe6_bare_arg0".to_string(),
            "__trust_vc_closure_arg0 > 100u64".to_string(),
            Some("closure_cross_contamination.rs:probe6".to_string()),
        );
    });
    assert!(
        !matches!(result, VerifyResult::Verified),
        "PROBE-6: bare `__trust_vc_closure_arg0 > 100` must NOT be vacuously \
         verified by a leaked precondition. Got: {result:?}"
    );
}

/// Three-closure chain: a correct guarded closure, a false-postcondition
/// closure, and another correct closure. The false one must sink the result.
#[test]
fn test_three_closure_chain_false_middle_is_rejected() {
    let result = common::verify_and_get_result(|| {
        let a = trust_vc::closure!(
            |x: u64|
            requires(x > 100u64)
            ensures(|res: u64| res == x)
            x
        );
        let _ = a(200u64);

        let bad = trust_vc::closure!(
            |y: u64|
            ensures(|res: u64| res > 1000u64)
            y
        );
        let _ = bad(7u64);

        let c = trust_vc::closure!(
            |z: u64|
            requires(z > 50u64)
            ensures(|res: u64| res > 50u64)
            z
        );
        let _ = c(60u64);
    });
    assert!(
        !matches!(result, VerifyResult::Verified),
        "three-closure chain with a false middle postcondition must be rejected, \
         got: {result:?}"
    );
}

/// A closure `requires` must not leak to *outer* (post-call) obligations.
#[test]
fn test_closure_requires_does_not_leak_to_outer_code() {
    let result = common::verify_and_get_result(|| {
        let a = trust_vc::closure!(
            |x: u64|
            requires(x > 100u64)
            ensures(|res: u64| res == x)
            x
        );
        let _ = a(200u64);

        // Outer code references the legacy shared param symbol directly.
        trust_vc_core::verify_macro::collect_variable(
            "__trust_vc_closure_arg0".to_string(),
            "u64".to_string(),
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "outer_uses_leaked_symbol".to_string(),
            "__trust_vc_closure_arg0 > 100u64".to_string(),
            Some("closure_cross_contamination.rs:outer".to_string()),
        );
    });
    assert!(
        !matches!(result, VerifyResult::Verified),
        "closure requires must not leak to outer code, got: {result:?}"
    );
}

// ── (b) No over-rejection: legitimate closures must still verify ──────

/// Single correct closure: requires assumed, ensures follows from body.
#[test]
fn test_single_correct_closure_still_verified() {
    common::with_clean_verification(|| {
        let guarded = trust_vc::closure!(
            |x: u64|
            requires(x > 100u64)
            ensures(|res: u64| res > 100u64)
            x
        );
        let _ = guarded(200u64);

        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "single correct guarded closure must verify, got: {verify_result:?}"
        );
    });
}

/// Legitimate multi-closure: each contract independently correct -> Verified.
#[test]
fn test_legitimate_multi_closure_all_correct_verified() {
    common::with_clean_verification(|| {
        let a = trust_vc::closure!(
            |x: u64|
            requires(x > 100u64)
            ensures(|res: u64| res > 100u64)
            x
        );
        let _ = a(200u64);

        let b = trust_vc::closure!(
            |x: u64|
            ensures(|res: u64| res == x)
            x
        );
        let _ = b(5u64);

        let c = trust_vc::closure!(
            |x: u64, y: u64|
            ensures(|res: u64| res == x + y)
            x + y
        );
        let _ = c(3u64, 4u64);

        let pipeline = VerificationPipeline::collect_from_macros();
        let verify_result = pipeline.verify();
        assert!(
            matches!(verify_result, VerifyResult::Verified),
            "legitimate independent multi-closure proof must verify, got: {verify_result:?}"
        );
    });
}

/// Closure ensures checked against its OWN body: `ensures(res == 7)` over body
/// `x` must be a counterexample (body binds result, ensures must follow).
#[test]
fn test_closure_ensures_vs_own_body_is_counterexample() {
    let result = common::verify_and_get_result(|| {
        let bad = trust_vc::closure!(
            |x: u64|
            ensures(|res: u64| res == 7u64)
            x
        );
        let _ = bad(42u64);
    });
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "ensures(res == 7) over body `x` must be a counterexample, got: {result:?}"
    );
}

/// `requires(false)` -> vacuous truth (Unknown), unchanged by the fix.
#[test]
fn test_requires_false_is_vacuous() {
    let result = common::verify_and_get_result(|| {
        let vac = trust_vc::closure!(
            |x: u64|
            requires(false)
            ensures(|res: u64| res == 7u64)
            x
        );
        let _ = vac(1u64);
    });
    assert!(
        matches!(result, VerifyResult::Unknown { .. }),
        "requires(false) should be vacuous (Unknown), got: {result:?}"
    );
}
