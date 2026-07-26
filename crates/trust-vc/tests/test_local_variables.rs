// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for local variable tracking in proof functions (issue #578).
//!
//! This addresses the fundamental problem where local variables were
//! invisible to the verifier because only function parameters were declared.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verify_macro::track_local_variable;
use trust_vc_core::VerifyResult;

/// Test that explicitly tracked local variables are visible to verification.
mod common;

#[test]
fn test_tracked_local_variables() {
    common::with_clean_verification(|| {
        // Create a verification context
        let mut ctx = VerificationContext::new();

        // Declare function parameter
        ctx.declare_var_parsed("x", "i32");

        // Track a local variable using the new API
        ctx.declare_var_parsed("y", "i32");

        // Prevent BV overflow: x < i32::MAX ensures x + 1 doesn't wrap
        ctx.push_assume("no_overflow", "x < 2147483647");

        // Add the relationship between variables
        ctx.push_assume("y_definition", "y == x + 1");

        // Add assertion about the local variable
        ctx.push_assert("y_greater_than_x", "y > x");

        // Verify - this should work because y is declared
        let result = ctx.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Local variables should verify when properly declared, got: {:?}",
            result
        );
    })
}

/// Test the new track_local_variable function.
#[test]
fn test_track_local_variable_api() {
    common::with_clean_verification(|| {
        // Track function parameter
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Track local variable
        track_local_variable("y".to_string(), "i32".to_string());

        // Collect an assertion using the local variable
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "local_var_test".to_string(),
            "y == x + 1".to_string(),
            Some("test:1".to_string()),
        );

        // Add assumption about y's value
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "y_value".to_string(),
            "y == x + 1".to_string(),
            Some("test:2".to_string()),
        );

        // Verify collected obligations
        let result = trust_vc_core::verify_macro::verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Track_local_variable should allow verification of local variables, got: {:?}",
            result
        );
    })
}

/// Test that untracked local variables cause verification to fail.
#[test]
fn test_untracked_local_variables_fail() {
    common::with_clean_verification(|| {
        // Create a verification context
        let mut ctx = VerificationContext::new();

        // Only declare function parameter
        ctx.declare_var_parsed("x", "i32");

        // DO NOT declare local variable y
        // This simulates the old broken behavior

        // Add assertion about the undeclared local variable
        ctx.push_assert("y_greater_than_x", "y > x");

        // Verify - this should fail because y is not declared
        let result = ctx.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "Untracked local variables should cause verification to fail, but got: {:?}",
            result
        );
    })
}

/// Test using the typed obligation API with local variables.
#[test]
fn test_typed_obligations_with_locals() {
    common::with_clean_verification(|| {
        use trust_vc_core::verify_macro::collect_typed_obligation;

        // Track function parameter - use i32 instead of u64 for simpler arithmetic
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Track local variables
        track_local_variable("sum".to_string(), "i32".to_string());

        // Add assumption that n > 0 and bounded to prevent BV overflow
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_positive".to_string(),
            "n > 0".to_string(),
            None,
        );
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "n_bounded".to_string(),
            "n < 1073741824".to_string(), // < i32::MAX/2 prevents n+n overflow
            None,
        );

        // Add assumptions about local variable values
        trust_vc_core::verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "sum_def".to_string(),
            "sum == n + n".to_string(),
            None,
        );

        // Use the typed obligation API for assertions
        collect_typed_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "sum_greater".to_string(),
            "sum > n".to_string(), // This uses parseable Rust code, not stringify!
            Some("test:10".to_string()),
        );

        // Verify collected obligations
        let result = trust_vc_core::verify_macro::verify_collected();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Typed obligations with local variables should verify, got: {:?}",
            result
        );
    })
}

/// Test that demonstrates the fix for issue #578.
///
/// This test shows that with proper AST-based tracking, local variables
/// can be used in verification, addressing the fundamental limitation
/// where stringify! destroyed all type information.
#[test]
fn test_issue_578_fixed() {
    common::with_clean_verification(|| {
        // This test demonstrates the solution to issue #578:
        // "SOLUTION: Replace stringify! with syn-based AST parsing"

        let mut ctx = VerificationContext::new();

        // Function parameter
        ctx.declare_var_parsed("x", "i32");

        // Local variables are now trackable!
        ctx.declare_var_parsed("a", "i32");
        ctx.declare_var_parsed("b", "i32");
        ctx.declare_var_parsed("c", "i32");

        // Define relationships
        ctx.push_assume("a_def", "a == x * 2");
        ctx.push_assume("b_def", "b == a + 1");
        ctx.push_assume("c_def", "c == b * b");

        // These assertions now work because variables are declared
        ctx.push_assert("a_correct", "a == x * 2");
        ctx.push_assert("b_correct", "b == a + 1");
        ctx.push_assert("c_correct", "c == b * b");

        let result = ctx.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Issue #578 fix: Local variables should verify with AST-based approach, got: {:?}",
            result
        );
    })
}
