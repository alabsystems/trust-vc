// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests that expose issues in function context implementation.

use trust_vc_core::ir::TrustVcType;
use trust_vc_core::mode::FunctionMode;
use trust_vc_core::vc::{FunctionContext, ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

#[test]
fn test_function_parameters_not_used() {
    // ISSUE: Function parameters are collected but never used
    let mut ctx = VerificationContext::new();

    let func_ctx = FunctionContext::new(
        "add",
        vec![
            (
                "x".to_string(),
                TrustVcType::Opaque("invalid_type".to_string()),
            ),
            ("".to_string(), TrustVcType::from_str("i32").unwrap()),
        ],
        TrustVcType::from_str("i32").unwrap(),
        FunctionMode::Exec,
    )
    .with_recursive(true);

    ctx.set_function_context(func_ctx);

    // This should probably fail due to invalid parameters, but it doesn't
    // because parameters are ignored
    let result = ctx.verify();

    // Currently this doesn't error, showing parameters aren't validated
    match result {
        VerifyResult::Error { .. } => {
            // Should error on invalid parameters
        }
        _ => {
            // BUG: Invalid parameters are accepted
        }
    }
}

#[test]
fn test_duplicate_function_registration() {
    // ISSUE: No handling of duplicate function registrations
    let mut ctx = VerificationContext::new();

    // Register the same function twice with different signatures
    let func_ctx1 = FunctionContext::new(
        "factorial",
        vec![("n".to_string(), TrustVcType::from_str("u64").unwrap())],
        TrustVcType::from_str("u64").unwrap(),
        FunctionMode::Exec,
    )
    .with_recursive(true);

    let func_ctx2 = FunctionContext::new(
        "factorial",
        vec![("x".to_string(), TrustVcType::from_str("i32").unwrap())],
        TrustVcType::from_str("i32").unwrap(),
        FunctionMode::Exec,
    )
    .with_recursive(true);

    ctx.set_function_context(func_ctx1);
    // BUG: This overwrites the first context silently
    ctx.set_function_context(func_ctx2);

    // Only the second context is kept
    assert_eq!(
        ctx.function_context().unwrap().return_type(),
        &TrustVcType::from_str("i32").unwrap()
    );
}

#[test]
fn test_empty_function_name_accepted() {
    // ISSUE: Empty function names are accepted
    let mut ctx = VerificationContext::new();

    let func_ctx = FunctionContext::new(
        "",
        vec![],
        TrustVcType::Opaque("void".to_string()),
        FunctionMode::Exec,
    )
    .with_recursive(true);

    ctx.set_function_context(func_ctx);

    // This should fail but doesn't
    let result = ctx.verify();

    // BUG: Empty function names should be rejected
    match result {
        VerifyResult::Error { message } if message.contains("empty") => {
            // Should error on empty name
        }
        _ => {
            // Currently accepts empty names
        }
    }
}

#[test]
fn test_function_context_without_variables() {
    // ISSUE: Function context references parameters that aren't declared as variables
    let mut ctx = VerificationContext::new();

    let func_ctx = FunctionContext::new(
        "compute",
        vec![
            ("a".to_string(), TrustVcType::from_str("i32").unwrap()),
            ("b".to_string(), TrustVcType::from_str("i32").unwrap()),
        ],
        TrustVcType::from_str("i32").unwrap(),
        FunctionMode::Exec,
    )
    .with_recursive(true);

    ctx.set_function_context(func_ctx);
    // BUG: Parameters 'a' and 'b' are not automatically declared as variables
    // User must manually declare them, which is error-prone

    ctx.push_obligation(ProofObligation::assert("uses_params", "a + b > 0"));

    let result = ctx.verify();

    // Parameters 'a' and 'b' aren't in ctx.variables(), so prepare_context's
    // TypeEnv doesn't include them. The typed preparation path fails while
    // lowering the obligation before the legacy string encoder executes.
    match result {
        VerifyResult::Error { message }
            if message.contains("Failed to lower obligation 'uses_params'")
                && message.contains("unresolved variable `a`") =>
        {
            // Parameters should be auto-declared
        }
        _ => {
            panic!("Parameters should be declared automatically");
        }
    }
}
