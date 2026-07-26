// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for proper requires semantics in function body verification.
//!
//! With VerificationMode::BodyLevel (default), Requires is an assumption:
//! - requires(false) makes any postcondition vacuously true
//! - requires(P) + ensures(Q) verifies if P implies Q
//!
//! Fixes #1692: these tests previously required #[should_panic] workarounds
//! because Requires was always treated as an assertion.

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_requires_false_makes_function_unreachable() {
    common::with_clean_verification(|| {
        // In Hoare logic, requires(false) means the function can never be called.
        // This makes ANY postcondition vacuously true (ex falso quodlibet).
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "impossible_precondition".to_string(),
            "false".to_string(),
            None,
        );

        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "absurd_postcondition".to_string(),
            "1 == 2".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #2258: requires(false) makes assumptions contradictory → vacuous truth detected
        assert!(
            matches!(result, VerifyResult::Unknown { ref reason, .. } if reason.contains("vacuously true")),
            "requires(false) + ensures(1==2) should be detected as vacuously true, got: {:?}",
            result
        );
    })
}

#[test]
fn test_requires_creates_assumption_not_assertion() {
    common::with_clean_verification(|| {
        // Proper semantics: requires creates an assumption for function body verification
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "precondition".to_string(),
            "x > 10".to_string(),
            None,
        );

        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "x > 0".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // BodyLevel mode: x > 10 is assumed, x > 0 trivially follows
        assert!(
            matches!(result, VerifyResult::Verified),
            "requires(x > 10) + ensures(x > 0) should verify in BodyLevel mode, got: {:?}",
            result
        );
    })
}

#[test]
fn test_body_level_requires_false_is_vacuously_verified() {
    common::with_clean_verification(|| {
        // In BodyLevel mode, requires(false) alone has no assertions → vacuously Verified
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_false".to_string(),
            "false".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #808/#2258: assumptions-only context (no assertions) → Error
        assert!(
            matches!(result, VerifyResult::Error { .. }),
            "requires(false) with no assertions should return Error (nothing to prove), got: {:?}",
            result
        );
    })
}

#[test]
fn test_body_level_requires_assumption_enables_ensures() {
    common::with_clean_verification(|| {
        // BodyLevel mode: requires(x > 0) assumed, ensures(x > -10) should verify
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "precondition".to_string(),
            "x > 0".to_string(),
            None,
        );

        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "postcondition".to_string(),
            "x > -10".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "requires(x > 0) + ensures(x > -10) should verify in BodyLevel mode, got: {:?}",
            result
        );
    })
}
