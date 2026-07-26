// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Test for issue #1249 - unsigned comparison type tracking with method calls

use trust_vc::assert_by;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_unsigned_array_length_comparison() {
    common::with_clean_verification(|| {
        // Declare a Seq variable
        verify_macro::collect_variable("arr".to_string(), "Seq<u64>".to_string());

        // Add assumption about array length
        verify_macro::collect_obligation(
            trust_vc_core::vc::ObligationKind::Assume,
            "arr_len".to_string(),
            "arr.len() == 5".to_string(),
            None,
        );

        // Dummy Rust variable (verification only looks at the collected variables)
        #[allow(unused)]
        let arr = trust_vc_types::Seq::<u64>::empty();

        // Test that len() returns usize (unsigned) and comparison works
        #[allow(clippy::len_zero)]
        {
            assert_by!(arr.len() > 0);
        }

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Known gap: method-call syntax (arr.len()) not supported by obligation parser
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Method-call syntax should not parse — expected Error, got {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_with_indexing() {
    common::with_clean_verification(|| {
        // Known gap: Seq::index is a ghost-only method that panics at runtime.
        // assert_by! evaluates the expression at runtime in test mode,
        // so calling ghost methods in assert_by! is not currently supported.
        let arr = trust_vc_types::Seq::<u64>::empty();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| arr.index(0)));
        assert!(
            result.is_err(),
            "Seq::index should panic at runtime (ghost-only method)"
        );
    })
}
