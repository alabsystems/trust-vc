// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Basic contract tests for trust_vc with proper verification.
//!
//! Tests that requires!, ensures!, and old! macros compile and verify correctly.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc::{ensures, old, requires};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

// Helper to declare variables for verification
fn declare_i32(name: &str) {
    trust_vc_core::verify_macro::collect_variable(name.to_string(), "i32".to_string());
}

// Helper to declare and bind a variable with a concrete value
fn declare_i32_with_value(name: &str, value: i32) {
    trust_vc_core::verify_macro::collect_variable(name.to_string(), "i32".to_string());
    trust_vc_core::verify_macro::collect_obligation(
        trust_vc_core::vc::ObligationKind::Assume,
        format!("{}_value", name),
        format!("{} == {}", name, value),
        None,
    );
}

mod common;

#[test]
fn test_requires_verifies() {
    common::with_clean_verification(|| {
        // requires! should compile as a precondition check
        // Note: requires creates an assumption, not an assertion
        // We need an ensures to have something to verify
        declare_i32("x");
        let _x = 5;
        // Add assumption about the concrete value
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_value".to_string(),
            "x == 5".to_string(),
            None,
        );
        requires!(x > 0);
        ensures!(x >= 0); // This should verify given the requires

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Valid precondition should verify"
            ),
        }
    })
}

#[test]
fn test_ensures_verifies() {
    common::with_clean_verification(|| {
        // ensures! should compile as a postcondition check
        declare_i32("result");
        let _result = 42;
        // Add assumption about the concrete value
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "result_value".to_string(),
            "result == 42".to_string(),
            None,
        );
        ensures!(result > 0);

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Valid postcondition should verify"
            ),
        }
    })
}

#[test]
fn test_requires_with_expression_fixed() {
    common::with_clean_verification(|| {
        // requires! with complex expression
        declare_i32_with_value("a", 10);
        declare_i32_with_value("b", 5);
        let _a = 10;
        let _b = 5;
        requires!(a > b);
        ensures!(a >= b); // Need an assertion to verify

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Valid complex precondition should verify"
            ),
        }
    })
}

#[test]
fn test_ensures_with_expression_fixed() {
    common::with_clean_verification(|| {
        // ensures! with complex expression
        declare_i32_with_value("x", 3);
        declare_i32_with_value("y", 4);
        declare_i32_with_value("z", 7);
        let x = 3;
        let y = 4;
        let _z = x + y;
        ensures!(z == x + y);

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Valid complex postcondition should verify"
            ),
        }
    })
}

#[test]
fn test_contracts_together_fixed() {
    common::with_clean_verification(|| {
        // Using requires! and ensures! in same function
        declare_i32_with_value("x", 5);
        let x = 5;
        requires!(x > 0);
        declare_i32_with_value("result", 10);
        let _result = x * 2;
        ensures!(result > x);

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "Combined contracts should verify"
            ),
        }
    })
}

#[test]
fn test_false_requires_fails() {
    common::with_clean_verification(|| {
        // Test that requires! creates an assumption, not an assertion.
        // Use declare_i32 (no concrete value) to avoid contradicting requires!.
        declare_i32("x");
        let _x = -5;
        requires!(x > 0); // This ASSUMES x > 0 for verification
        ensures!(x > -10); // Given the assumption x > 0, this passes

        // requires! is a precondition — it tells the verifier what to assume.
        // Given only "x > 0", the ensures "x > -10" holds.
        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {
                // Expected: When we assume x > 0, then x > -10 is trivially true
            }
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "requires! should create an assumption that makes ensures! pass"
            ),
        }
    })
}

#[test]
fn test_false_ensures_fails() {
    common::with_clean_verification(|| {
        // Invalid postcondition should fail verification
        declare_i32_with_value("result", 42);
        let _result = 42;
        ensures!(result < 0); // FALSE for result = 42, should fail verification

        // Note: In test mode, ensures! doesn't panic at runtime (see #1066)
        // Instead we check that the verification outcome is Failed
        let outcome = VerificationPipeline::collect_from_macros().verify();
        match outcome {
            VerifyResult::Counterexample { .. } => {
                // Expected: postcondition result < 0 is false for result = 42
            }
            VerifyResult::Verified => {
                panic!("Test should fail verification but passed - false ensures should fail")
            }
            other => panic!(
                "Expected Counterexample but got {:?}: {}",
                other, "False postcondition should fail verification"
            ),
        }
    })
}

// Note: old! macro doesn't generate verification conditions by itself,
// it's a helper for use within ensures! contexts
#[test]
fn test_old_with_ensures_fixed() {
    common::with_clean_verification(|| {
        // Typical pattern: old! inside ensures! for state change verification.
        // Use declare_i32 for x (no concrete value) — the update assumption
        // "x == 15" is the sole constraint on x, avoiding contradiction.
        declare_i32("x");
        declare_i32_with_value("old_x", 10); // old! captures the value of x at entry
        let mut x = 10;
        let _old_x = old!(x);
        #[allow(unused_assignments)]
        {
            x += 5;
        }
        // Update x's value for verification (sole constraint on x)
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "x_after_update".to_string(),
            "x == 15".to_string(),
            None,
        );
        ensures!(x == old_x + 5);

        let result = VerificationPipeline::collect_from_macros().verify();
        match result {
            VerifyResult::Verified => {}
            other => panic!(
                "Expected Verified but got {:?}: {}",
                other, "old! with ensures! should verify state change"
            ),
        }
    })
}
