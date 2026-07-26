// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test that demonstrates issue #182: assert! macro behavior
//!
//! This test shows that false assertions don't actually "pass" -
//! they would fail at runtime due to the dual collection/check behavior.

mod common;

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verify_macro::{collect_obligation, verify_collected};
use trust_vc_core::VerifyResult;

#[test]
fn test_false_assertion_collection_only() {
    // Test collecting a false obligation without runtime check
    common::with_clean_verification(|| {
        // Collect a false assertion directly - bypasses runtime assert
        collect_obligation(
            ObligationKind::Assert,
            "false_claim".to_string(),
            "5 > 10".to_string(), // This is false!
            Some("test:24:1".to_string()),
        );

        let result = verify_collected();

        // The verification should correctly detect this is false and return a counterexample
        // This test was incorrect - false assertions should NOT verify
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Expected false assertion to return counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_true_assertion_verifies() {
    common::with_clean_verification(|| {
        collect_obligation(
            ObligationKind::Assert,
            "true_claim".to_string(),
            "10 > 5".to_string(), // This is true
            Some("test:46:1".to_string()),
        );

        let result = verify_collected();
        assert!(matches!(result, VerifyResult::Verified));
    })
}

#[test]
#[should_panic(expected = "trust_vc assertion failed")]
#[allow(clippy::assertions_on_constants)]
fn test_macro_would_panic_on_false() {
    // This demonstrates that the trust_vc::assert! macro
    // would panic at runtime for false assertions

    // Simulate what the macro expands to:
    #[cfg(test)]
    {
        collect_obligation(
            ObligationKind::Assert,
            "assert_line_99".to_string(),
            "5 > 10".to_string(),
            Some("test:99:1".to_string()),
        );

        // The macro ALSO does this runtime check which fails!
        assert!(5 > 10, "trust_vc assertion failed: {}", "5 > 10");
    }
}

/// Malformed expressions panic at collection time per #1723 invariant.
/// Expressions come from stringify!() and are always valid Rust syntax.
#[test]
fn test_invalid_syntax_panics() {
    trust_vc_core::verify_macro::clear_all_thread_locals();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        collect_obligation(
            ObligationKind::Assert,
            "malformed".to_string(),
            "(5 + 1 > 3".to_string(), // Missing closing paren — invalid Rust syntax
            Some("test:83:1".to_string()),
        );
    }));

    trust_vc_core::verify_macro::clear_all_thread_locals();

    assert!(
        result.is_err(),
        "Malformed expression should panic per #1723"
    );
    let err = result.unwrap_err();
    let msg = err
        .downcast_ref::<String>()
        .map(|s| s.as_str())
        .unwrap_or("");
    assert!(
        msg.contains("#1723"),
        "Panic should reference #1723, got: {}",
        msg
    );
}
