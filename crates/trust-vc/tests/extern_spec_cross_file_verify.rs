// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Explicit bridge tests for cross-file extern_spec verification.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline.

mod common;
#[path = "extern_spec_cross_file_verify/support.rs"]
mod support;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[test]
fn test_verify_extern_call_imports_cross_file_requires_into_pipeline() {
    common::with_clean_verification(|| {
        let _ = trust_vc_core::verify_extern_call!("u32::count_ones", 5_u32.count_ones());

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "cross-file requires(false) should reach ay as a failing assertion, got: {result:?}"
        );
    })
}
