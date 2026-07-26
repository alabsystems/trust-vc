// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

fn verify_with_pipeline(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

#[test]
fn test_str_view_len_reflexive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "str");
    ctx.push_assert("view_len_reflexive", "s.view().len() == s.view().len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "str view len should verify, got: {:?}",
        result
    );
}

#[test]
fn test_string_view_len_reflexive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "String");
    ctx.push_assert("view_len_reflexive", "s.view().len() == s.view().len()");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "String view len should verify, got: {:?}",
        result
    );
}

#[test]
fn test_string_view_contains_char_reflexive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "String");
    ctx.push_assert(
        "view_contains_char_reflexive",
        "s.view().contains('a') == s.view().contains('a')",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(
            result,
            VerifyResult::Verified | VerifyResult::Unknown { .. }
        ),
        "String view contains(char) should at least lower and reach the solver, got: {:?}",
        result
    );
}

#[test]
fn test_string_len_requires_view() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "String");
    ctx.push_assert("len_without_view", "s.len() == 0");

    let result = verify_with_pipeline(ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("view()"),
                "String::len rejection should point callers to view(), got: {}",
                message
            );
        }
        other => panic!("Direct String::len() must fail closed, got: {:?}", other),
    }
}

#[test]
fn test_str_len_requires_view() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("s", "str");
    ctx.push_assert("len_without_view", "s.len() == 0");

    let result = verify_with_pipeline(ctx);
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains("view()"),
                "str::len rejection should point callers to view(), got: {}",
                message
            );
        }
        other => panic!("Direct str::len() must fail closed, got: {:?}", other),
    }
}
