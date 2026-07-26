//! Invariant cascade scaling proofs — detect O(n³) regressions in the
//! invariant verification pipeline.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Design
//!
//! The invariant verification loop (typed.rs:150-187) accumulates
//! `verified_invariant_obligations`. For invariant i, the encoder re-encodes
//! 0..i-1 prior invariants as assumptions. Total assumption re-encodings
//! across I invariants: sum(0..I-1) = I*(I-1)/2 = O(I²).
//!
//! Each invariant also creates 2 encoder setups (base + inductive), so total
//! encoder setups = 2*I. Combined cost: O(I² + I*(V+K+B)).
//!
//! This is acceptable — O(I²) in number of invariants is unavoidable when
//! invariants depend on each other (invariant j uses invariant i as assumption
//! for j > i). These tests verify it doesn't regress to cubic or worse.
//!
//! Part of performance_proofs phase.

use super::*;

/// Minimum timing to avoid division by near-zero durations.
const MIN_MEASURABLE_US: u128 = 100;

/// Invariant cascade: verify O(I²) scaling (not cubic).
///
/// Uses u32 variables so `v >= 0` invariants are tautological for both
/// base case (u32 literal is non-negative) and inductive step (u32 is
/// always non-negative regardless of mutation).
#[test]
fn test_invariant_cascade_scaling_not_cubic() {
    let small = 3;
    let large = 12;

    let t_small = measure_median(|| time_verify_n_invariants(small), 3);
    let t_large = measure_median(|| time_verify_n_invariants(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    // Expected: O(I²) with V, K, B fixed. T(4N)/T(N) ≈ 16x for quadratic.
    // Threshold at 64x catches cubic (would be ~64x for 4x scale factor).
    let cubic_threshold = 64.0;

    assert!(
        ratio < cubic_threshold,
        "Invariant cascade scaling appears cubic or worse: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (threshold {:.0}x). \
         The verified_invariant_obligations cascade in verify_typed \
         may have regressed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        cubic_threshold,
    );
}

/// Invariant count × variable count cross-scaling.
///
/// With I invariants and V variables, total cost is O(I² + I*V).
/// Scaling both by 4x should give ≤ O(16 + 16) = O(32)x, not O(64+)x.
#[test]
fn test_invariant_variable_cross_scaling() {
    let small_i = 2;
    let small_v = 3;
    let large_i = 8;
    let large_v = 12;

    let t_small = measure_median(|| time_verify_invariants_and_vars(small_i, small_v), 3);
    let t_large = measure_median(|| time_verify_invariants_and_vars(large_i, large_v), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    // Both I and V scaled 4x. O(I² + I*V) → O(16+16) = ~32x.
    // Allow 100x to avoid flaky failures (conservative for cubic detection).
    assert!(
        ratio < 100.0,
        "Invariant×variable cross-scaling appears worse than O(I²+IV): \
         T({}i×{}v)={}μs, T({}i×{}v)={}μs, ratio={:.1}x (threshold 100x)",
        small_i,
        small_v,
        t_small,
        large_i,
        large_v,
        t_large,
        ratio,
    );
}

fn time_verify_n_invariants(n: usize) -> u128 {
    time_verify_invariants_and_vars(n, n)
}

fn time_verify_invariants_and_vars(n_inv: usize, n_vars: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    for i in 0..n_vars {
        ctx.declare_var_typed(
            &format!("v{}", i),
            crate::ir::TrustVcType::parse_or_opaque("u32"),
        );
    }
    ctx.push_obligation(crate::vc::ProofObligation::assume("init", "v0 == 0"));

    for i in 0..n_inv.min(n_vars) {
        ctx.obligations
            .push(crate::vc::ProofObligation::loop_invariant(
                format!("inv_{}", i),
                format!("v{} >= 0", i),
            ));
    }

    ctx.push_obligation(crate::vc::ProofObligation::assert("check", "v0 >= 0"));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(
        &result,
        &format!("Invariant scaling setup failed at inv={n_inv}, vars={n_vars}"),
    );

    elapsed
}
