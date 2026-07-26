//! Verification workflow tests: verify_collected, verify_proof_impl,
//! verify_markers_impl, collect_and_verify, decreases workflow.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::context_management::with_clean_thread_locals;
use crate::vc::ObligationKind;

#[test]
fn test_verify_collected_with_empty_context() {
    with_clean_thread_locals(|| {
        // Calling verify_collected with no context should return an error
        let result = verify_collected();

        // With no context initialized, it should return an error
        match result {
            crate::encoder::VerifyResult::Error { message } => {
                assert!(
                    message.contains("No verification context initialized"),
                    "Expected 'No verification context initialized' error, got: {}",
                    message
                );
            }
            _ => panic!(
                "Expected Error result for cleared context, got: {:?}",
                result
            ),
        }
    });
}

#[test]
fn test_verify_collected_with_assumptions_only_context_returns_error() {
    with_clean_thread_locals(|| {
        collect_obligation(
            ObligationKind::Assume,
            "assume_only".to_string(),
            "false".to_string(),
            None,
        );

        let result = verify_collected();
        match result {
            crate::encoder::VerifyResult::Error { message } => {
                assert!(
                    message.contains("only assumptions and no assertions"),
                    "Assumptions-only context must return Error, got: {}",
                    message
                );
            }
            _ => panic!(
                "Expected Error for assumptions-only context, got: {:?}",
                result
            ),
        }
    });
}

#[test]
fn test_verify_collected_with_trivial_assertion() {
    with_clean_thread_locals(|| {
        // Add a trivially true assertion
        collect_obligation(
            ObligationKind::Assert,
            "trivial".to_string(),
            "true".to_string(),
            None,
        );

        // Verify it — "true" is a boolean literal, should verify immediately
        let result = verify_collected();
        assert!(
            matches!(result, crate::encoder::VerifyResult::Verified),
            "Trivially true assertion should verify, got: {:?}",
            result
        );
    });
}

#[test]
fn test_verify_proof_impl() {
    use std::fs;
    use std::path::Path;

    // Create a temporary test file
    let test_dir = Path::new("target/test_verify_proof_impl");
    fs::create_dir_all(test_dir).unwrap();
    let test_file = test_dir.join("test_proof.rs");

    // Write a simple Rust file with markers
    fs::write(
        &test_file,
        r#"
            #[__trust_vc_ensures = "true"]
            fn simple_proof() {
                // Always true
            }
        "#,
    )
    .unwrap();

    // Test verify_proof_impl
    let result = verify_proof_impl("simple_proof", "test::module", test_file.to_str().unwrap());

    // Clean up
    fs::remove_file(&test_file).ok();

    // BUG: verify_proof_impl currently returns error for marker files because
    // marker extraction doesn't produce obligations. Assert current behavior
    // so the test catches when this is fixed (flip to is_ok).
    assert!(
        result.is_err(),
        "verify_proof_impl should currently error (empty context bug), got: {:?}",
        result
    );
}

#[test]
fn test_verify_markers_impl_no_markers() {
    use std::fs;
    use std::path::Path;

    // Create a temporary test file
    let test_dir = Path::new("target/test_verify_markers_impl");
    fs::create_dir_all(test_dir).unwrap();
    let test_file = test_dir.join("no_markers.rs");

    // Write a Rust file without markers
    fs::write(
        &test_file,
        r#"
            fn regular_function() {
                println!("No markers here");
            }
        "#,
    )
    .unwrap();

    // Test verify_markers_impl
    let result = verify_markers_impl("test::module", test_file.to_str().unwrap());

    // Clean up
    fs::remove_file(&test_file).ok();

    // Should return an error when no markers are found (fixes #1518)
    assert!(
        result.is_err(),
        "verify_markers_impl should fail when no markers found, got: {:?}",
        result
    );
    let err_msg = result.unwrap_err();
    assert!(
        err_msg.contains("No trust_vc verification markers found"),
        "Error should mention missing markers, got: {}",
        err_msg
    );
}

#[test]
fn test_verify_markers_impl_with_markers() {
    use std::fs;
    use std::path::Path;

    // Create a temporary test file
    let test_dir = Path::new("target/test_verify_markers_with_markers");
    fs::create_dir_all(test_dir).unwrap();
    let test_file = test_dir.join("with_markers.rs");

    // Write a Rust file with markers — use bounded x to avoid BV overflow
    // at i32::MAX which causes valid counterexample
    fs::write(
        &test_file,
        r#"
            #[__trust_vc_requires = "x > 0 && x < 100"]
            #[__trust_vc_ensures = "x + 1 > 0"]
            fn increment(x: i32) -> i32 {
                x + 1
            }
        "#,
    )
    .unwrap();

    // Test verify_markers_impl
    let result = verify_markers_impl("test::module", test_file.to_str().unwrap());

    // Clean up
    fs::remove_file(&test_file).ok();

    // verify_markers_impl should return Ok (markers found and processed)
    assert!(
        result.is_ok(),
        "verify_markers_impl should succeed for file with markers, got: {:?}",
        result
    );
}

#[test]
fn test_verify_markers_impl_rejects_malformed_marker_even_with_other_valid_markers() {
    use std::fs;
    use std::path::Path;

    // Regression for #1884: a malformed marker must not be silently treated
    // as absent when another marker parses successfully.
    let test_dir = Path::new("target/test_verify_markers_malformed_marker");
    fs::create_dir_all(test_dir).unwrap();
    let test_file = test_dir.join("malformed_with_valid.rs");

    fs::write(
        &test_file,
        r#"
            #[__trust_vc_requires = 123]
            #[__trust_vc_ensures = "true"]
            fn malformed_with_valid_marker(x: i32) -> i32 {
                x
            }
        "#,
    )
    .unwrap();

    let result = verify_markers_impl("test::module", test_file.to_str().unwrap());

    fs::remove_file(&test_file).ok();

    assert!(
        result.is_err(),
        "malformed marker must fail source extraction, got: {:?}",
        result
    );
    let err_msg = result.unwrap_err();
    assert!(
        err_msg.contains("Malformed marker #[__trust_vc_requires]"),
        "error should identify malformed marker, got: {}",
        err_msg
    );
}

#[test]
fn test_collect_and_verify_workflow() {
    // Test a complete workflow
    with_clean_thread_locals(|| {
        // Collect some variables
        collect_variable("x".to_string(), "u32".to_string());
        collect_variable("y".to_string(), "u32".to_string());

        // Add assumptions
        collect_obligation(
            ObligationKind::Assume,
            "assume_x".to_string(),
            "x > 0".to_string(),
            None,
        );

        collect_obligation(
            ObligationKind::Assume,
            "assume_y".to_string(),
            "y > 0".to_string(),
            None,
        );

        // Add assertion
        collect_obligation(
            ObligationKind::Assert,
            "assert_sum".to_string(),
            "x + y > 0".to_string(),
            None,
        );

        // Verify: x + y > 0 does NOT hold for u32 due to unsigned overflow
        // (e.g., x = 0xFFFFFFFF, y = 1 → x + y wraps to 0).
        // The solver should find this counterexample.
        let result = verify_collected();
        assert!(
            matches!(result, crate::encoder::VerifyResult::Counterexample { .. }),
            "x + y > 0 with u32 overflow should produce counterexample, got: {:?}",
            result
        );
    });
}

#[test]
fn test_decreases_workflow() {
    with_clean_thread_locals(|| {
        // Simulate a decreases verification workflow
        collect_variable("n".to_string(), "u64".to_string());

        // Collect the measure
        collect_decreases_measure("n".to_string(), Some("factorial.rs:5".to_string()));

        // Add decrease check for recursive call
        collect_decrease_obligation("factorial_rec", "n - 1 < n", Some("factorial.rs:7"));

        // Also test verify_decreases
        verify_decreases("factorial", "n".to_string(), "n - 1".to_string());

        // Verify context has obligations
        let ctx = get_context();
        assert!(ctx.is_some());
    });
}

#[test]
fn test_parallel_obligation_collection() {
    // Test that we can collect many obligations efficiently
    with_clean_thread_locals(|| {
        // Collect 100 obligations
        for i in 0..100 {
            collect_obligation(
                if i % 3 == 0 {
                    ObligationKind::Assume
                } else if i % 3 == 1 {
                    ObligationKind::Assert
                } else {
                    ObligationKind::Requires
                },
                format!("obligation_{}", i),
                format!("var_{} > 0", i),
                Some(format!("test.rs:{}", i)),
            );
        }

        // Context should exist
        assert!(get_context().is_some());
    });
}
