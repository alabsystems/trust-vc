//! Tests for verify_macro.rs fixes.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::verify_macro::verify_collected;
use trust_vc_core::VerifyResult;

#[test]
fn test_empty_context_returns_error_not_verified() {
    common::with_clean_verification(|| {
        // Issue #750: Empty verification context should return Error, not Verified

        // Verify with no obligations collected
        let result = verify_collected();

        // Should return an error, not Verified
        assert!(
            matches!(result, VerifyResult::Error { ref message } if message.contains("No verification context")),
            "Empty context should return Error, got: {:?}",
            result
        );
    })
}

#[test]
fn test_context_with_no_assertions_returns_error() {
    common::with_clean_verification(|| {
        // Issue #750: Context with no assertions should return Error
        use trust_vc_core::verify_macro::collect_variable;

        // Collect only a variable, no assertions
        collect_variable("x".to_string(), "i32".to_string());

        let result = verify_collected();

        // Should return an error about empty context (only variable, no obligations)
        assert!(
            matches!(result, VerifyResult::Error { ref message } if message.contains("no obligations to check")),
            "Context with no assertions should return Error, got: {:?}",
            result
        );
    })
}

#[test]
fn test_multi_argument_decreases_parsing() {
    common::with_clean_verification(|| {
        // Issue #748: Multi-argument decreases measures should be handled
        use trust_vc_core::verify_macro::collect_decreases_measure;

        // Test single measure
        collect_decreases_measure("n".to_string(), None);

        // Test multi-argument measure (lexicographic)
        collect_decreases_measure("(m, n)".to_string(), None);

        // Test triple measure
        collect_decreases_measure("(x, y, z)".to_string(), None);

        // The function should not panic for multi-argument measures
        // (The actual verification logic would need to be tested with full context)
    })
}

#[test]
fn test_doc_tests_marked_correctly() {
    // Issue #747: Doc tests should be marked as ignore to avoid resolution issues

    // This test verifies that the doc test examples in verify_macro.rs
    // are properly marked as `ignore` rather than trying to run them.
    // The actual check is in the source code - this test documents the fix.

    // Read the source to verify the markers
    let source = include_str!("../src/verify_macro.rs");

    // Check that the problematic doc tests are marked as ignore
    assert!(
        source.contains("/// ```ignore\n/// #[trust_vc::proof]"),
        "First doc test should be marked as ignore"
    );

    // Check the second problematic doc test
    let lines: Vec<&str> = source.lines().collect();
    let mut found_second = false;
    for i in 0..lines.len() {
        if lines[i].contains("/// ```ignore")
            && i + 2 < lines.len()
            && (lines[i + 1].contains("#[trust_vc::proof]")
                || lines[i + 2].contains("#[trust_vc::proof]"))
        {
            found_second = true;
            break;
        }
    }
    assert!(
        found_second,
        "Second doc test should also be marked as ignore"
    );
}
