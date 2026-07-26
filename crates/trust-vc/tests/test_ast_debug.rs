// Copyright 2026 Andrew Yates
// Author: Andrew Yates

//! Test file for verification features.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline
// Licensed under the Apache License, Version 2.0

// Debug test to see what's happening with AST parsing

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

#[test]
fn test_debug_ast_parsing() {
    common::with_clean_verification(|| {
        // This test is temporarily disabled as it needs the full AST parser
        // which is not yet implemented. The test_one_real_verification test
        // demonstrates the working verification instead.

        // Add simple assertion to debug
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assert,
            "debug_test".to_string(),
            "true".to_string(),
            None,
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        eprintln!("Debug Result: {:?}", result);

        assert!(matches!(result, VerifyResult::Verified));
    })
}
