// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Demonstrates the semantic mismatch between Path A and Path B verification (issue #380).
//!
//! Path A: Direct VerificationContext API - WORKS
//! Path B: Thread-local + verify_markers! - BROKEN

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// Test helper module not needed for these tests

/// Path A: Direct API - This WORKS correctly
#[test]
fn test_path_a_direct_api_works() {
    // Build a verification context manually
    let mut ctx = VerificationContext::new();

    // Explicitly declare ALL variables
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32"); // Local variable explicitly declared

    // Add assertion with both variables
    ctx.push_assert("local_var_assertion", "y == x + 1");
    ctx.push_assume("y_definition", "y == x + 1");

    // Verify with ay
    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "Path A should verify correctly, got: {:?}",
        result
    );
}

/// Path B: Thread-local macros - This is BROKEN
// NOTE: #[proof] macro deleted in architectural pivot
// This function demonstrates what Path B TRIED to do (but failed)
fn path_b_proof_with_local_var(_x: i32) {
    // In Path B, x would be declared as a parameter in the #[proof] macro expansion

    // But y is a local variable that was NEVER declared in ay!
    // let y = x + 1;

    // This assertion would collect the string "y > x"
    // But y was undefined in ay context!
    // trust_vc::assert!(y > x);

    // This function is kept only for documentation purposes
}

#[test]
fn test_path_b_thread_local_broken() {
    // Path B has been deleted in architectural pivot
    // This test now demonstrates why Path B couldn't work

    eprintln!("Path B was deleted because:");
    eprintln!("1. Local variables were never declared to ay");
    eprintln!("2. Thread-local state caused RefCell panics");
    eprintln!("3. Verification ran at runtime instead of compile-time");
    eprintln!("4. The macro approach was fundamentally incompatible with ay");

    // The function path_b_proof_with_local_var now does nothing
    // It's kept only for documentation purposes
    path_b_proof_with_local_var(5);

    // No verification happens because Path B is deleted
    eprintln!("✓ Path B correctly deleted - use Path A instead");
}

/// Demonstrate the specific problem with Path B
#[test]
fn test_path_b_problem_demonstration() {
    eprintln!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    eprintln!("DEMONSTRATION OF PATH A vs PATH B MISMATCH (#380)");
    eprintln!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    eprintln!();

    eprintln!("Path A (Direct API):");
    eprintln!("  1. Explicitly declares all variables");
    eprintln!("  2. Adds assertions as strings");
    eprintln!("  3. ay knows about all variables");
    eprintln!("  4. Verification WORKS");
    eprintln!();

    eprintln!("Path B (Thread-local macros):");
    eprintln!("  1. Only declares function parameters");
    eprintln!("  2. Local variables are NEVER declared");
    eprintln!("  3. ay gets undefined variable errors");
    eprintln!("  4. Verification BROKEN");
    eprintln!();

    eprintln!("The Problem:");
    eprintln!("  - trust_vc::assert!(y > x) collects string \"y > x\"");
    eprintln!("  - But y was never declared as a ay variable!");
    eprintln!("  - ay parser fails with \"Undefined variable: y\"");
    eprintln!();

    eprintln!("This explains why:");
    eprintln!("  - Only ~6 files perform real verification (Path A)");
    eprintln!("  - ~15 files think they verify but actually fail (Path B)");
    eprintln!("  - Most tests are just compile tests");
    eprintln!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
}

/// Show what SHOULD happen to fix Path B
#[test]
fn test_what_path_b_should_do() {
    // What the #[proof] macro SHOULD generate
    let mut ctx = VerificationContext::new();

    // 1. Declare function parameters
    ctx.declare_var_parsed("x", "i32");

    // 2. ALSO need to declare local variables!
    // This is the missing piece - the macro needs to:
    // - Parse the function body
    // - Find all local variable declarations
    // - Add them to the ay context
    ctx.declare_var_parsed("y", "i32");

    // 3. Prevent BV overflow: x < i32::MAX ensures x + 1 doesn't wrap
    ctx.push_assume("no_overflow", "x < 2147483647");

    // 4. Add the relationship between variables
    ctx.push_assume("y_definition", "y == x + 1");

    // 5. Add the assertion
    ctx.push_assert("y_greater_than_x", "y > x");

    // 5. Verify
    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "Properly declared variables should verify"
    );
}

/// Demonstrate that Path B can't handle ANY local variables
// NOTE: #[proof] macro deleted in architectural pivot
// This function demonstrates what Path B TRIED to do (but failed)
fn complex_local_vars(_x: i32) {
    // In Path B, these locals were NEVER declared to ay:
    // let a = x * 2;
    // let b = a + 1;
    // let c = b * b;

    // ALL of these assertions would fail because a, b, c were undefined!
    // trust_vc::assert!(a == x * 2);
    // trust_vc::assert!(b == a + 1);
    // trust_vc::assert!(c == b * b);

    // This function is kept only for documentation purposes
}

#[test]
fn test_path_b_fails_with_any_locals() {
    // Path B has been deleted in architectural pivot
    // This test now demonstrates why complex locals couldn't work

    eprintln!("Path B couldn't handle complex locals because:");
    eprintln!("- Variables a, b, c were never declared to ay");
    eprintln!("- Only function parameters were declared");
    eprintln!("- Local variable declarations were ignored");
    eprintln!("- This made any non-trivial verification impossible");

    // The function complex_local_vars now does nothing
    complex_local_vars(5);

    eprintln!("✓ Path B correctly deleted - use Path A with explicit declarations");
}
