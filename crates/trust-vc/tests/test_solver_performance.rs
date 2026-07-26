// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test to profile ay solver performance and identify bottlenecks.

use std::time::Instant;
use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

#[test]
fn test_solver_initialization_overhead() {
    // Measure verification time for simple assertions
    let iterations = 10;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.push_assert("identity", "x + 0 == x");

    // Warm up and verify correctness
    let warmup_result = ctx.verify();
    assert!(
        matches!(warmup_result, VerifyResult::Verified),
        "x + 0 == x should verify (BV identity), got: {:?}",
        warmup_result
    );

    let start = Instant::now();
    for _ in 0..iterations {
        let result = ctx.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "x + 0 == x should verify consistently, got: {:?}",
            result
        );
    }
    let elapsed = start.elapsed();

    let avg_verify_time = elapsed.as_secs_f64() / iterations as f64;
    assert!(
        avg_verify_time < 1.0,
        "Verification is too slow: {:.3}s",
        avg_verify_time
    );
}

#[test]
fn test_multiple_verifications() {
    // Test multiple different verifications to simulate what happens in test suite
    let test_cases: Vec<(&str, &str, bool)> = vec![
        ("simple_true", "x + 0 == x", true),
        ("simple_false", "x == x + 1", false),
        ("complex", "x * 2 == x + x", true),
        ("inequality", "x > 0 || x <= 0", true),
        ("tautology", "x == x", true),
    ];

    let mut total_time = 0.0;
    for (name, condition, should_verify) in &test_cases {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_parsed("x", "i32");
        ctx.push_assert(name, condition);

        let start = Instant::now();
        let result = ctx.verify();
        let elapsed = start.elapsed();

        if *should_verify {
            assert!(
                matches!(result, VerifyResult::Verified),
                "Test case '{}' ({}) should verify, got: {:?}",
                name,
                condition,
                result
            );
        } else {
            assert!(
                matches!(result, VerifyResult::Counterexample { .. }),
                "Test case '{}' ({}) should produce counterexample, got: {:?}",
                name,
                condition,
                result
            );
        }

        total_time += elapsed.as_secs_f64();
    }

    assert!(
        total_time < 5.0,
        "Total verification time is too slow: {:.3}s",
        total_time
    );
}
