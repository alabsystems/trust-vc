// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Negative tests for loop invariant verification
//!
//! These tests verify that invalid loop invariants are properly rejected
//! and produce appropriate counterexamples.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline

use trust_vc::invariant;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

#[path = "test_verify_helpers_v2.rs"]
mod test_verify_helpers_v2;
use test_verify_helpers_v2::expect_counterexample;

mod common;

#[test]
fn test_invariant_not_maintained_fails() {
    common::with_clean_verification(|| {
        // Declare variable
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());

        // Invariant that's not maintained - i stays even
        let mut i = 0;
        while i < 10 {
            invariant!(i % 2 == 0); // Claims i is always even
            i += 1; // But we increment by 1, making it odd
        }

        let (_obligation_name, _model) = expect_counterexample()
            .expect("Invariant not maintained should produce counterexample");
    })
}

#[test]
fn test_invariant_false_initially_fails() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("x".to_string(), "i32".to_string());

        // Invariant that's false from the start
        let mut x = 10;
        while x > 0 {
            invariant!(x < 5); // False initially since x starts at 10
            x -= 1;
        }

        let (_obligation_name, _model) = expect_counterexample()
            .expect("Initially false invariant should produce counterexample");
    })
}

#[test]
fn test_invariant_becomes_false_fails() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("count".to_string(), "i32".to_string());
        trust_vc_core::verify_macro::collect_variable("_limit".to_string(), "i32".to_string());

        // Invariant that becomes false during execution
        let mut count = 0;
        let _limit = 5;
        while count <= 10 {
            invariant!(count <= _limit); // Becomes false when count > 5
            count += 1;
        }

        let (_obligation_name, _model) = expect_counterexample()
            .expect("Invariant that becomes false should produce counterexample");
    })
}

#[test]
fn test_invariant_contradicts_loop_condition_fails() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("n".to_string(), "i32".to_string());

        // Invariant contradicts the loop condition
        let mut n = 0;
        while n < 100 {
            invariant!(n >= 100); // Contradicts n < 100
            n += 10;
        }

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();
        // We need to check the result directly since we already called verify()
        match result {
            VerifyResult::Counterexample { .. } => {}
            other => panic!("Contradictory invariant should fail, got: {:?}", other),
        }
    })
}

#[test]
fn test_multiple_conflicting_invariants_fail() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("v".to_string(), "i32".to_string());

        // Multiple invariants that conflict
        let mut v = 0;
        while v < 20 {
            invariant!(v < 10); // First invariant
            invariant!(v >= 10); // Conflicting invariant
            v += 1;
        }

        let (_obligation_name, _model) =
            expect_counterexample().expect("Conflicting invariants should produce counterexample");
    })
}

#[test]
fn test_invariant_with_overflow_fails() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("big".to_string(), "i32".to_string());

        // Invariant that would cause overflow
        let mut big = i32::MAX - 5;
        while big < i32::MAX {
            invariant!(big + 10 > big); // Would overflow when big is near MAX
            big += 1;
        }

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Overflow handling might produce error or counterexample
        assert!(
            !matches!(result, VerifyResult::Verified),
            "Invariant with overflow should not verify"
        );
    })
}
