// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Explicit bridge tests for same-package extern_spec verification.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline.

trust_vc::extern_spec! {
    impl i32 {
        #[requires(false)]
        fn abs(self) -> i32;

        #[requires(true)]
        #[ensures(true)]
        fn signum(self) -> i32;
    }
}

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[test]
fn test_verify_extern_call_imports_requires_into_pipeline() {
    common::with_clean_verification(|| {
        let _ = trust_vc_core::verify_extern_call!("i32::abs", (-5_i32).abs());

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "requires(false) should reach ay as a failing assertion, got: {result:?}"
        );
    })
}

#[test]
fn test_verify_extern_call_imports_positive_contracts_into_pipeline() {
    common::with_clean_verification(|| {
        let _ = trust_vc_core::verify_extern_call!("i32::signum", (-5_i32).signum());

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "literal true contracts should verify through the bridge, got: {result:?}"
        );
    })
}

#[test]
fn test_verify_extern_call_fails_loudly_on_lexical_path_mismatch() {
    common::with_clean_verification(|| {
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = trust_vc_core::verify_extern_call!("core::primitive::i32::abs", (-5_i32).abs());
        }))
        .expect_err("lexical mismatch should panic instead of silently dropping contracts");

        let message = if let Some(message) = panic.downcast_ref::<String>() {
            message.clone()
        } else if let Some(message) = panic.downcast_ref::<&str>() {
            message.to_string()
        } else {
            "unknown panic".to_string()
        };

        assert!(
            message.contains("current package rooted at"),
            "panic should explain the searched package boundary, got: {message}"
        );
        assert!(
            message.contains("dependency crates are not searched"),
            "panic should explain the unsupported dependency-crate boundary, got: {message}"
        );
    })
}
