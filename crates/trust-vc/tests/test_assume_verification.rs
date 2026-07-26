// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for assume! macro verification behavior
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file verify that assume! works correctly as an assumption

use trust_vc_core::vc::{ObligationKind, VerificationMode};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_assume_enables_proof() {
    common::with_clean_verification(|| {
        // Test that assumptions enable proofs to succeed
        // Declare variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Assume x > 10
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_x_large".to_string(),
            "x > 10".to_string(),
            Some("test_assume:assume".to_string()),
        );

        // Assert x > 5 (should pass because we assumed x > 10)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_x_gt_5".to_string(),
            "x > 5".to_string(),
            Some("test_assume:assert".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Assertion should verify with assumption, got: {:?}",
            result
        );
    })
}

#[test]
fn test_assume_false_makes_everything_verify() {
    common::with_clean_verification(|| {
        // Test ex falso quodlibet - assuming false makes everything verify
        // Assume false
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_false".to_string(),
            "false".to_string(),
            Some("test_assume:false".to_string()),
        );

        // Assert something impossible (should verify because we assumed false)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_impossible".to_string(),
            "1 == 2".to_string(),
            Some("test_assume:impossible".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #2258: contradictory assumptions are now detected as vacuous truth
        assert!(
            matches!(result, VerifyResult::Unknown { ref reason, .. } if reason.contains("vacuously true")),
            "Contradictory assumptions should be detected as vacuously true, got: {:?}",
            result
        );
    })
}

#[test]
fn test_contradictory_assumptions_verify_vacuously() {
    common::with_clean_verification(|| {
        // Test that contradictory assumptions make everything verify
        // Declare variable
        verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Add contradictory assumptions
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_x_large".to_string(),
            "x > 100".to_string(),
            Some("test_assume:large".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_x_small".to_string(),
            "x < 50".to_string(),
            Some("test_assume:small".to_string()),
        );

        // Assert anything (should verify vacuously due to contradiction)
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_anything".to_string(),
            "x == 75".to_string(), // Impossible given the assumptions
            Some("test_assume:assert".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #2258: contradictory assumptions are now detected as vacuous truth
        assert!(
            matches!(result, VerifyResult::Unknown { ref reason, .. } if reason.contains("vacuously true")),
            "Contradictory assumptions should be detected as vacuously true, got: {:?}",
            result
        );
    })
}

#[test]
fn test_assume_vs_requires_difference() {
    // Part 1: Assume(false) + Assert(true) → Verified (false assumption, vacuous truth)
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_false".to_string(),
            "5 > 10".to_string(),
            Some("test_assume:vs_requires".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_true".to_string(),
            "true".to_string(),
            Some("test_assume:vs_requires".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // #2258: contradictory assumptions (5>10 is false) detected as vacuous truth
        assert!(
            matches!(result, VerifyResult::Unknown { ref reason, .. } if reason.contains("vacuously true")),
            "Contradictory assumptions should be detected as vacuously true, got: {:?}",
            result
        );
    });

    // Part 2: Requires(false) in CallSite mode → Counterexample (must be satisfiable)
    common::with_clean_verification(|| {
        verify_macro::collect_obligation(
            ObligationKind::Requires,
            "requires_false".to_string(),
            "5 > 10".to_string(),
            Some("test_assume:requires".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_true".to_string(),
            "true".to_string(),
            Some("test_assume:requires".to_string()),
        );

        let mut pipeline2 = VerificationPipeline::collect_from_macros();
        pipeline2
            .context_mut()
            .set_verification_mode(VerificationMode::CallSite);
        let result2 = pipeline2.verify();

        assert!(
            matches!(result2, VerifyResult::Counterexample { .. }),
            "Requires false should fail verification in CallSite mode, got: {:?}",
            result2
        );
    })
}

#[test]
fn test_assume_chain_reasoning() {
    common::with_clean_verification(|| {
        // Test that assumptions can be chained for reasoning
        // Declare variables
        verify_macro::collect_variable("x".to_string(), "i32".to_string());
        verify_macro::collect_variable("y".to_string(), "i32".to_string());
        verify_macro::collect_variable("z".to_string(), "i32".to_string());

        // Chain of assumptions
        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_x_gt_y".to_string(),
            "x > y".to_string(),
            Some("test_assume:chain1".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_y_gt_z".to_string(),
            "y > z".to_string(),
            Some("test_assume:chain2".to_string()),
        );

        verify_macro::collect_obligation(
            ObligationKind::Assume,
            "assume_z_positive".to_string(),
            "z > 0".to_string(),
            Some("test_assume:chain3".to_string()),
        );

        // Assert transitive property
        verify_macro::collect_obligation(
            ObligationKind::Assert,
            "assert_x_positive".to_string(),
            "x > 0".to_string(), // Should follow from x > y > z > 0
            Some("test_assume:chain_result".to_string()),
        );

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "Chained assumptions should enable transitive proof, got: {:?}",
            result
        );
    })
}
