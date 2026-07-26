//! Test that VerificationPipeline correctly handles empty context
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[test]
fn test_verification_pipeline_empty_context_returns_error() {
    common::with_clean_verification(|| {
        // Create a pipeline with no obligations
        let pipeline = VerificationPipeline::new();

        // Verify should return an error for empty context
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { ref message } if message.contains("empty context")),
            "Empty VerificationPipeline should return Error, got: {:?}",
            result
        );
    })
}

#[test]
fn test_verification_pipeline_collect_empty_returns_error() {
    common::with_clean_verification(|| {
        // Collect from macros when there are no obligations
        // (context is already cleared by with_clean_verification)
        let pipeline = VerificationPipeline::collect_from_macros();

        // Verify should return an error for empty context
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Error { ref message } if message.contains("empty context")),
            "Empty collected pipeline should return Error, got: {:?}",
            result
        );
    })
}
