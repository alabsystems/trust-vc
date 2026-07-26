// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Test verifying the fix for soundness bug #808 - empty contexts now return Error.
//!
//! This test verifies that the bug has been fixed.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

/// This test verifies the fix for soundness bug #808
#[test]
fn test_soundness_bug_808_fixed() {
    // Create an empty verification context
    let ctx = VerificationContext::new();

    // Verify that it has no assertions
    assert!(!ctx.has_assertions(), "Context should have no assertions");

    // Try to verify the empty context
    let result = ctx.verify();

    // After the fix, this should return Error
    match result {
        VerifyResult::Verified => {
            panic!("Bug not fixed: Empty context still returns Verified!");
        }
        VerifyResult::Error { message } => {
            // This is the correct behavior after the fix
            assert!(message.contains("empty") || message.contains("no assertions"));
            println!("✓ Fixed: Empty context correctly returns Error");
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}

/// Test with only assumptions (no assertions) - returns Error (nothing to prove)
/// #808/#2258: assumptions-only contexts have nothing to verify
#[test]
fn test_assumptions_only_correctly_verifies() {
    let mut ctx = VerificationContext::new();

    // Add only assumptions, no assertions
    ctx.push_assume("assumption1", "x > 0");
    ctx.push_assume("assumption2", "y < 10");

    assert!(!ctx.has_assertions(), "Should have no assertions");

    let result = ctx.verify();

    // #808/#2258: assumptions-only context → Error (nothing to prove)
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "Assumptions-only context should return Error (nothing to prove), got: {:?}",
        result
    );
}

/// Test that empty contexts now correctly return Error (additional verification)
#[test]
fn test_empty_context_error_message() {
    let ctx = VerificationContext::new();
    let result = ctx.verify();

    // Verify we get the right error message
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("Cannot verify empty context"),
                "Error message should indicate empty context, got: {}",
                message
            );
        }
        _ => panic!("Expected Error for empty context, got: {:?}", result),
    }
}

/// Valid contexts with assertions should still verify correctly
#[test]
fn test_valid_context_still_works() {
    let mut ctx = VerificationContext::new();

    // Add a valid assertion
    ctx.push_assert("valid", "5 > 3");

    let result = ctx.verify();

    // This should still work correctly
    assert_eq!(result, VerifyResult::Verified);
}
