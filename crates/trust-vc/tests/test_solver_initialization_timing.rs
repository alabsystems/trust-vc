// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Benchmark test to measure ay solver initialization overhead.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline

use std::time::Instant;
use trust_vc_core::vc::{ObligationKind, ProofObligation};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

/// Build a pipeline that verifies `(var + 1) > var` with BV overflow guard.
fn bv_safe_increment_pipeline(var: &str) -> VerificationPipeline {
    let mut pipeline = VerificationPipeline::new();
    pipeline.context_mut().declare_var_parsed(var, "i32");
    pipeline.add_obligation(ProofObligation::new(
        format!("assume_bounded_{}", var),
        format!("{} < 2147483647", var),
        ObligationKind::Assume,
    ));
    pipeline.add_obligation(ProofObligation::new(
        format!("assert_inc_{}", var),
        format!("({} + 1) > {}", var, var),
        ObligationKind::Assert,
    ));
    pipeline
}

#[test]
fn test_solver_initialization_timing() {
    // Measure time for single verification
    let start = Instant::now();
    let pipeline = bv_safe_increment_pipeline("x");
    let result = pipeline.verify();
    let single_verify_time = start.elapsed();

    assert_eq!(
        result,
        VerifyResult::Verified,
        "Single verification should pass"
    );
    eprintln!("Single verification time: {:?}", single_verify_time);

    // Measure time for 5 verifications
    let start = Instant::now();
    for i in 0..5 {
        let var = format!("x{}", i);
        let pipeline = bv_safe_increment_pipeline(&var);
        let result = pipeline.verify();
        assert_eq!(
            result,
            VerifyResult::Verified,
            "Verification {} should pass",
            i
        );
    }
    let five_verify_time = start.elapsed();

    eprintln!("Five verifications: {:?}", five_verify_time);
    eprintln!("Average per verification: {:?}", five_verify_time / 5);
}
