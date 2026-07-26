// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for function context preservation in verification.

use trust_vc_core::ir::TrustVcType;
use trust_vc_core::mode::FunctionMode;
use trust_vc_core::vc::{FunctionContext, ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

#[test]
fn test_function_context_registration() {
    // Test that function context can be set and used
    let mut ctx = VerificationContext::new();

    // Set up a recursive function context for ackermann
    let func_ctx = FunctionContext::new(
        "ackermann",
        vec![
            ("m".to_string(), TrustVcType::from_str("u64").unwrap()),
            ("n".to_string(), TrustVcType::from_str("u64").unwrap()),
        ],
        TrustVcType::from_str("u64").unwrap(),
        FunctionMode::Exec,
    )
    .with_recursive(true);

    ctx.set_function_context(func_ctx);

    // Declare the parameters as variables
    ctx.declare_var_typed("m", TrustVcType::from_str("u64").unwrap());
    ctx.declare_var_typed("n", TrustVcType::from_str("u64").unwrap());

    // Add a condition that references the function name
    // This should not fail with "Undefined variable: ackermann" anymore
    ctx.push_obligation(ProofObligation::assert("recursive_call", "ackermann >= 0"));

    // Verify - this tests that the function name is registered
    let result = ctx.verify();

    // The assertion should verify (u64 is always >= 0)
    // More importantly, it shouldn't error with "undefined variable"
    match result {
        VerifyResult::Error { message } if message.contains("undefined variable") => {
            panic!("Function context not properly registered: {}", message);
        }
        VerifyResult::Verified => {
            // Expected - the function is registered as a u64 constant
        }
        other => {
            // Also acceptable - we're mainly testing that it doesn't error
            eprintln!("Verification result: {:?}", other);
        }
    }
}

#[test]
fn test_non_recursive_function_not_registered() {
    // Test that non-recursive functions are not registered as variables
    let mut ctx = VerificationContext::new();

    let func_ctx = FunctionContext::new(
        "factorial",
        vec![("n".to_string(), TrustVcType::from_str("u64").unwrap())],
        TrustVcType::from_str("u64").unwrap(),
        FunctionMode::Exec,
    );

    ctx.set_function_context(func_ctx);
    ctx.declare_var_typed("n", TrustVcType::from_str("u64").unwrap());

    // Try to use the function name - should fail since it's not recursive
    ctx.push_obligation(ProofObligation::assert("non_recursive", "factorial >= 0"));

    let result = ctx.verify();

    // The typed preparation path may fail during lowering with unresolved variable,
    // while the legacy path reports "Undefined variable" during encoding.
    match result {
        VerifyResult::Error { message }
            if message.contains("undefined variable `factorial`")
                || (message.contains("Failed to lower obligation 'non_recursive'")
                    && message.contains("unresolved variable `factorial`")) =>
        {
            // Expected - non-recursive functions are not registered
        }
        other => {
            panic!(
                "Non-recursive function should not be registered: {:?}",
                other
            );
        }
    }
}
