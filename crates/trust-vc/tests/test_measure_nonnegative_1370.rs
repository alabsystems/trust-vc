// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test for issue #1370: MeasureNonNegative obligations not properly verified
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests that MeasureNonNegative properly rejects negative values.
//! Fixed (#1697): use add_assume (not add_assert) for constraints, and
//! require exact Counterexample for negative tests.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

#[test]
fn test_measure_nonnegative_with_negative_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "i32");

    // Assume n == -5 (constraint, not something to verify)
    ctx.push_assume("n_is_negative", "n == -5");

    // Measure check: n >= 0 should fail since n == -5
    ctx.add_measure_nonneg("n");

    let result = ctx.verify();

    // n==-5 contradicts n>=0 — solver must find a counterexample (#1697).
    match result {
        VerifyResult::Counterexample { .. } => {
            // Constrained to n==-5, so n>=0 is trivially false.
        }
        other => panic!(
            "n==-5 contradicts n>=0: must produce Counterexample, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_measure_nonnegative_with_positive_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "i32");

    // Assume n == 5 (constraint, not something to verify)
    ctx.push_assume("n_is_positive", "n == 5");

    // Measure check: n >= 0 should verify since n == 5
    ctx.add_measure_nonneg("n");

    let result = ctx.verify();

    match result {
        VerifyResult::Verified => {
            // n==5 satisfies n>=0.
        }
        other => panic!("n==5 implies n>=0: must produce Verified, got: {:?}", other),
    }
}

#[test]
fn test_measure_nonnegative_without_constraints() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "i32");

    // No constraints on n — n>=0 is trivially refutable (n=-1)
    ctx.add_measure_nonneg("n");

    let result = ctx.verify();

    // Free i32 n with no constraints — n>=0 is trivially refutable (#1697).
    match result {
        VerifyResult::Counterexample { .. } => {
            // Unconstrained i32: solver finds negative counterexample.
        }
        other => panic!(
            "Unconstrained i32 n>=0 must produce Counterexample, got: {:?}",
            other
        ),
    }
}
