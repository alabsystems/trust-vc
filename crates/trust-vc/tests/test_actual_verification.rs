// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test that demonstrates ACTUAL verification through ay, not just compilation.
//!
//! This test fixes the critical architectural failure where no verification
//! ever happened (#302). It creates a simple working verification pipeline:
//! 1. Define proof obligations
//! 2. Send them to ay at compile time (simulated here in test)
//! 3. Get verification results back
//! 4. Test that results are correct

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

#[test]
fn test_simple_true_assertion_verifies() {
    // Build a verification context manually (what the macros SHOULD do at compile time)
    let mut ctx = VerificationContext::new();

    // Declare a variable
    ctx.declare_var_parsed("x", "i32");

    // Add a true assertion
    ctx.push_assert("identity", "x + 0 == x");

    // Actually verify with ay!
    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Verified),
        "Identity property should verify, got: {:?}",
        result
    );
}

#[test]
fn test_false_assertion_fails() {
    let mut ctx = VerificationContext::new();

    // Declare variables
    ctx.declare_var_parsed("x", "i32");

    // Add a false assertion
    ctx.push_assert("false_claim", "x == x + 1");

    // Verify with ay
    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "False claim should produce counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_assumption_and_assertion() {
    let mut ctx = VerificationContext::new();

    // Declare variables
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");

    // Add assumption (precondition)
    ctx.push_assume("precondition", "x == y + 5");

    // Add assertion that follows from assumption
    ctx.push_assert("consequence", "x - y == 5");

    // Verify with ay
    let result = ctx.verify();

    // ay correctly verifies with assumption and assertion
    assert!(
        matches!(result, VerifyResult::Verified),
        "Expected Verified for assumption+assertion, got: {:?}",
        result
    );
}

#[test]
fn test_invalid_consequence_fails() {
    let mut ctx = VerificationContext::new();

    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");

    // Add assumption
    ctx.push_assume("precondition", "x > y");

    // Add assertion that does NOT follow
    ctx.push_assert("wrong_consequence", "x > y + 2");

    let result = ctx.verify();

    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Wrong consequence should fail, got: {:?}",
        result
    );
}

/// This is what a proof function SHOULD compile to:
/// Extract obligations at compile time and verify them.
fn what_proof_functions_should_do() {
    // At COMPILE TIME (via proc macro):
    // 1. Parse the proof function AST
    // 2. Extract variable declarations from parameters
    // 3. Extract assertions from trust_vc::assert! calls
    // 4. Build VerificationContext
    // 5. Call ay to verify
    // 6. Fail compilation if verification fails

    // This would be generated from:
    // #[proof]
    // fn lemma_commutative(x: i32, y: i32) {
    //     trust_vc::assert!(x + y == y + x);
    // }

    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");
    ctx.push_assert("commutative", "x + y == y + x");

    let result = ctx.verify();

    // At compile time, this should verify (commutative property of addition)
    assert!(
        matches!(result, VerifyResult::Verified),
        "Commutative property should verify at compile time, got: {:?}",
        result
    );
}

#[test]
fn test_what_proof_functions_should_do() {
    // This demonstrates the correct architecture
    what_proof_functions_should_do();
}
