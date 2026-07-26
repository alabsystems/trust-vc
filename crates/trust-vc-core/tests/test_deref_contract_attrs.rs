// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for dereference syntax inside contract attributes (#1856).
//!
//! Raw dereference still fails closed, but shared-reference parameters are
//! intentionally erased to their referent values with explicit provenance.

use syn::{parse_str, ItemFn};
use trust_vc_core::extract_verification_conditions;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

fn verify_extracted_function(code: &str) -> VerifyResult {
    let func = parse_str::<ItemFn>(code).expect("contract fixture should parse");
    let context =
        extract_verification_conditions(&func).expect("contract fixture should extract VCs");
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

fn assert_verified(result: VerifyResult) {
    assert!(
        matches!(result, VerifyResult::Verified),
        "expected verification success, got: {result:?}"
    );
}

fn assert_counterexample(result: VerifyResult) {
    match result {
        VerifyResult::Counterexample { .. } => {}
        other => {
            panic!("expected counterexample from transparent shared-ref deref, got: {other:?}")
        }
    }
}

fn assert_deref_error(result: VerifyResult) {
    match result {
        VerifyResult::Error { message } => {
            assert!(
                message.contains(
                    "dereference expressions are only supported for erased immutable reference variables"
                ),
                "expected dereference fail-closed error, got: {message}"
            );
        }
        other => panic!("expected dereference fail-closed error, got: {other:?}"),
    }
}

#[test]
fn test_requires_attr_deref_on_erased_shared_ref_verifies() {
    let result = verify_extracted_function(
        r#"
        #[requires(*x > 0)]
        #[ensures(result >= 0)]
        fn with_ref(x: &i32) -> i32 {
            0
        }
    "#,
    );

    assert_verified(result);
}

#[test]
fn test_ensures_attr_deref_on_erased_shared_ref_checks_value() {
    let result = verify_extracted_function(
        r#"
        #[requires(x >= 0)]
        #[ensures(result > *x)]
        fn with_ref_result(x: &i32) -> i32 {
            1
        }
    "#,
    );

    assert_counterexample(result);
}

#[test]
fn test_requires_attr_deref_without_erased_ref_fails_closed() {
    let result = verify_extracted_function(
        r#"
        #[requires(*x > 0)]
        #[ensures(result >= 0)]
        fn with_value(x: i32) -> i32 {
            0
        }
    "#,
    );

    assert_deref_error(result);
}
