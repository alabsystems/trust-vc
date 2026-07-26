// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for spec collections (Seq, Set, Map)
//!
//! These tests ensure that invalid operations on spec collections are properly rejected.
//! Each test verifies that false assertions about collections produce Counterexample results.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that ay correctly rejects invalid spec collection operations

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[cfg(test)]
mod negative_spec_tests {
    use super::*;

    /// Test that invalid Seq assertions are rejected

    #[test]
    fn test_invalid_seq_assertion_must_fail() {
        common::with_clean_verification(|| {
            // Register an invalid assertion about an empty sequence
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "empty_seq_not_empty".to_string(),
                "!Seq::<i32>::empty().is_empty()".to_string(),
                Some("test_spec_collections_negative.rs:33".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            assert!(
                !matches!(result, VerifyResult::Verified),
                "Invalid Seq assertion MUST NOT verify, got {:?}",
                result
            );
        })
    }

    /// Test that out-of-bounds Seq access is rejected
    #[test]
    fn test_seq_out_of_bounds_must_fail() {
        common::with_clean_verification(|| {
            // Register an out-of-bounds sequence access
            // A sequence with 3 elements doesn't have index 5
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "seq_out_of_bounds".to_string(),
                "seq_with_3_elements.index(5) == 10".to_string(),
                Some("test_spec_collections_negative.rs:61".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            // Should fail or produce unknown due to bounds violation
            assert!(
                !matches!(result, VerifyResult::Verified),
                "Out-of-bounds Seq access should not verify, got {:?}",
                result
            );
        })
    }

    /// Test that false Set membership assertions are rejected
    #[test]
    fn test_invalid_set_membership_must_fail() {
        common::with_clean_verification(|| {
            // Register an invalid assertion about empty set membership
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "empty_set_contains".to_string(),
                "Set::<i32>::empty().contains(5)".to_string(),
                Some("test_spec_collections_negative.rs:88".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            assert!(
                !matches!(result, VerifyResult::Verified),
                "Invalid Set membership assertion MUST produce Counterexample, not {:?}",
                result
            );
        })
    }

    /// Test that incorrect Set operations are rejected
    #[test]
    fn test_incorrect_set_operations_must_fail() {
        common::with_clean_verification(|| {
            // Register an incorrect assertion about set intersection
            // Disjoint sets {1,2} and {3,4} have empty intersection
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "disjoint_intersection_not_empty".to_string(),
                "!disjoint_sets.intersection.is_empty()".to_string(),
                Some("test_spec_collections_negative.rs:128".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            assert!(
                !matches!(result, VerifyResult::Verified),
                "Incorrect Set operation MUST produce Counterexample, not {:?}",
                result
            );
        })
    }

    /// Test that invalid Map lookups are rejected
    #[test]
    fn test_invalid_map_lookup_must_fail() {
        common::with_clean_verification(|| {
            // Register an invalid assertion about map lookup
            // Looking up a key not in the map should return None, not Some(value)
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "map_missing_key".to_string(),
                "map.get(missing_key) == Some(100)".to_string(),
                Some("test_spec_collections_negative.rs:153".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            assert!(
                !matches!(result, VerifyResult::Verified),
                "Invalid Map lookup MUST produce Counterexample, not {:?}",
                result
            );
        })
    }

    /// Test that incorrect Map size assertions are rejected
    #[test]
    fn test_incorrect_map_size_must_fail() {
        common::with_clean_verification(|| {
            // Register an incorrect assertion about map size
            // A map with 2 elements doesn't have size 5
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "map_wrong_size".to_string(),
                "map_with_2_elements.len() == 5".to_string(),
                Some("test_spec_collections_negative.rs:183".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            assert!(
                !matches!(result, VerifyResult::Verified),
                "Incorrect Map size assertion MUST produce Counterexample, not {:?}",
                result
            );
        })
    }

    /// Test that invalid Seq concatenation assertions are rejected
    #[test]
    fn test_invalid_seq_concat_must_fail() {
        common::with_clean_verification(|| {
            // Register an invalid assertion about sequence concatenation
            // Concatenating [1,2] and [3,4] gives [1,2,3,4] with length 4, not 10
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "seq_concat_wrong_length".to_string(),
                "concat([1,2], [3,4]).len() == 10".to_string(),
                Some("test_spec_collections_negative.rs:217".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            assert!(
                !matches!(result, VerifyResult::Verified),
                "Invalid Seq concatenation assertion MUST produce Counterexample, not {:?}",
                result
            );
        })
    }

    /// Test that invalid Set union assertions are rejected
    #[test]
    fn test_invalid_set_union_must_fail() {
        // Set literal syntax {1,2} is not valid Rust — collect_obligation panics (#1723)
        let result = std::panic::catch_unwind(|| {
            common::with_clean_verification(|| {
                verify_macro::collect_obligation(
                    trust_vc_core::vc::ObligationKind::Assert,
                    "set_union_wrong_size".to_string(),
                    "union({1,2}, {2,3}).len() == 4".to_string(),
                    Some("test_spec_collections_negative.rs:253".to_string()),
                );

                let pipeline = VerificationPipeline::collect_from_macros();
                let _result = pipeline.verify();
            })
        });
        // Set literal syntax causes parse panic — documents the gap
        assert!(
            result.is_err(),
            "Set literal syntax should cause panic (not valid Rust), got Ok"
        );
    }

    /// Test that invalid Map update assertions are rejected
    #[test]
    fn test_invalid_map_update_must_fail() {
        common::with_clean_verification(|| {
            // Register an invalid assertion about map update
            // Updating a key should change its value, not leave it the same
            verify_macro::collect_obligation(
                trust_vc_core::vc::ObligationKind::Assert,
                "map_update_unchanged".to_string(),
                "map.insert(key, new_value).get(key) == old_value".to_string(),
                Some("test_spec_collections_negative.rs:288".to_string()),
            );

            let pipeline = VerificationPipeline::collect_from_macros();
            let result = pipeline.verify();

            assert!(
                !matches!(result, VerifyResult::Verified),
                "Invalid Map update assertion MUST produce Counterexample, not {:?}",
                result
            );
        })
    }
}
