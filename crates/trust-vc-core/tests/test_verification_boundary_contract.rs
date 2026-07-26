// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for the canonical verification boundary contract (#1934).

mod common;

use std::fs;
use std::path::Path;
use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verify::Verifier;
use trust_vc_core::VerifyResult;

const EMPTY_CONTEXT_MESSAGE: &str = "Cannot verify empty context: no obligations to check";

fn assert_empty_context_error(result: VerifyResult, path: &str) {
    match result {
        VerifyResult::Error { message } => {
            assert_eq!(
                message, EMPTY_CONTEXT_MESSAGE,
                "{path} should use the canonical empty-context message"
            );
        }
        other => panic!("{path} should return Error for an empty context, got: {other:?}"),
    }
}

#[test]
fn test_empty_context_message_is_shared_across_public_wrappers() {
    common::with_clean_verification(|| {
        let ctx = VerificationContext::new();
        assert_empty_context_error(ctx.verify(), "VerificationContext::verify()");
        assert_empty_context_error(Verifier::verify_context(&ctx), "Verifier::verify_context()");

        let test_dir = Path::new("target/test_verification_boundary_contract");
        fs::create_dir_all(test_dir).unwrap();
        let test_file = test_dir.join("empty.rs");
        fs::write(
            &test_file,
            r#"
                fn empty() {}
            "#,
        )
        .unwrap();

        let result = trust_vc_core::verify_function_from_file(test_file.to_str().unwrap(), "empty")
            .expect("empty function should parse and extract successfully");
        assert_empty_context_error(result, "verify_function_from_file()");

        fs::remove_dir_all(test_dir).ok();
    });
}
