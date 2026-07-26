// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for extern_spec! macro
//!
//! These tests verify that incorrect extern_spec usage is properly rejected.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_extern_spec_violated_requires() {
    common::with_clean_verification(|| {
        // Test that violating extern_spec requires clause is caught
        // Simulate calling Option::unwrap on None
        // The test simulates: we have is_some == false (None)
        // and we're checking that unwrap's requires(is_some) fails

        // Define the is_some variable first
        verify_macro::collect_variable("is_some".to_string(), "bool".to_string());

        // Assume we have None (is_some == false)
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "option_is_none".to_string(),
            "is_some == false".to_string(),
            Some("extern_spec_negative:unwrap_none".to_string()),
        );

        // Assert that unwrap's precondition (is_some) holds
        // This should fail because is_some is false
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "unwrap_requires".to_string(),
            "is_some".to_string(), // Assert is_some (which is false)
            Some("extern_spec_negative:unwrap_none".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Calling unwrap on None should violate requires, got: {:?}",
            result
        );
    })
}

#[test]
fn test_extern_spec_violated_ensures() {
    common::with_clean_verification(|| {
        // Test that extern_spec ensures clause violations are caught
        // Simulate Vec::len() with incorrect ensures
        // Define the len variable
        verify_macro::collect_variable("len".to_string(), "usize".to_string());

        // Set actual length to 5
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "vec_len_actual".to_string(),
            "len == 5".to_string(),
            Some("extern_spec_negative:vec_len_ensures".to_string()),
        );

        // But ensures claims len > 10 (incorrect)
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "vec_len_ensures".to_string(),
            "len > 10".to_string(),
            Some("extern_spec_negative:vec_len_ensures".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Incorrect ensures for Vec::len should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_extern_spec_index_out_of_bounds() {
    common::with_clean_verification(|| {
        // Test that index out of bounds is caught with extern_spec
        // Vec has length 3
        verify_macro::collect_variable("vec_len".to_string(), "usize".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "vec_len".to_string(),
            "vec_len == 3".to_string(),
            Some("extern_spec_negative:index_oob".to_string()),
        );

        // Try to access index 5 (out of bounds)
        // Assert the precondition for indexing (should fail)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "index_in_bounds".to_string(),
            "5 < vec_len".to_string(), // This will fail: 5 < 3 is false
            Some("extern_spec_negative:index_oob".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Index out of bounds should be rejected, got: {:?}",
            result
        );
    })
}

#[test]
fn test_extern_spec_pop_empty_vec() {
    common::with_clean_verification(|| {
        // Test that Vec::pop on empty vector violates requires
        // Vec is empty
        verify_macro::collect_variable("vec_len".to_string(), "usize".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "vec_empty".to_string(),
            "vec_len == 0".to_string(),
            Some("extern_spec_negative:pop_empty".to_string()),
        );

        // Vec::pop requires len > 0
        // Assert the precondition (should fail)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "pop_requires".to_string(),
            "vec_len > 0".to_string(), // This will fail: 0 > 0 is false
            Some("extern_spec_negative:pop_empty".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Vec::pop on empty vector should violate requires, got: {:?}",
            result
        );
    })
}

#[test]
fn test_extern_spec_result_unwrap_err() {
    common::with_clean_verification(|| {
        // Test that Result::unwrap on Err violates requires
        // Result is Err
        verify_macro::collect_variable("is_ok".to_string(), "bool".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "result_is_err".to_string(),
            "is_ok == false".to_string(),
            Some("extern_spec_negative:unwrap_err".to_string()),
        );

        // Result::unwrap requires is_ok()
        // Assert the precondition (should fail)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "unwrap_requires_ok".to_string(),
            "is_ok".to_string(), // This will fail since is_ok is false
            Some("extern_spec_negative:unwrap_err".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Result::unwrap on Err should violate requires, got: {:?}",
            result
        );
    })
}

#[test]
fn test_extern_spec_contradictory_specs() {
    common::with_clean_verification(|| {
        // Test that contradictory extern specs are caught
        // First spec: ensures result > 0
        verify_macro::collect_variable("result".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "spec1_ensures".to_string(),
            "result > 0".to_string(),
            Some("extern_spec_negative:contradictory".to_string()),
        );

        // Second spec for same function: ensures result < 0
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "spec2_ensures".to_string(),
            "result < 0".to_string(),
            Some("extern_spec_negative:contradictory".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "Contradictory extern specs should fail, got: {:?}",
            result
        );
    })
}

#[test]
fn test_extern_spec_abs_negative_overflow() {
    common::with_clean_verification(|| {
        // Test that i32::abs on i32::MIN causes overflow
        // Set x to i32::MIN
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("result".to_string(), "i32".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "x_is_min".to_string(),
            "x == -2147483648".to_string(), // i32::MIN
            Some("extern_spec_negative:abs_overflow".to_string()),
        );

        // abs() should ensure result >= 0, but i32::MIN.abs() overflows
        verify_macro::collect_obligation(
            ObligationKind::Ensures,
            "abs_ensures".to_string(),
            "result >= 0 && result == -x".to_string(), // This can't be satisfied for i32::MIN
            Some("extern_spec_negative:abs_overflow".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "i32::abs on MIN should not verify due to overflow, got: {:?}",
            result
        );
    })
}

#[test]
fn test_extern_spec_slice_get_unchecked() {
    common::with_clean_verification(|| {
        // Test that slice::get_unchecked with invalid index is caught
        // Slice has length 10
        verify_macro::collect_variable("slice_len".to_string(), "usize".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "slice_len".to_string(),
            "slice_len == 10".to_string(),
            Some("extern_spec_negative:get_unchecked".to_string()),
        );

        // Try to get_unchecked at index 15 (unsafe!)
        // Assert the precondition for get_unchecked (should fail)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "get_unchecked_requires".to_string(),
            "15 < slice_len".to_string(), // This will fail: 15 < 10 is false
            Some("extern_spec_negative:get_unchecked".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "get_unchecked with invalid index should fail requires, got: {:?}",
            result
        );
    })
}

#[test]
fn test_extern_spec_hashmap_get_missing_key() {
    common::with_clean_verification(|| {
        // Test that HashMap::get requires are properly enforced
        // HashMap does not contain key "foo"
        verify_macro::collect_variable("contains_foo".to_string(), "bool".to_string());
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "map_no_foo".to_string(),
            "contains_foo == false".to_string(),
            Some("extern_spec_negative:hashmap_get".to_string()),
        );

        // Try to unwrap the result of get("foo")
        // Assert the precondition for unwrapping (should fail)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "get_requires_key".to_string(),
            "contains_foo".to_string(), // This will fail (it's false)
            Some("extern_spec_negative:hashmap_get".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "HashMap::get on missing key should fail when unwrapped, got: {:?}",
            result
        );
    })
}
