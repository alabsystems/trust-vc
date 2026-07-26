//! Component scaling tests: broadcast cap, combined A×V, infer_int_width,
//! invariant cascade, and literal count scaling.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from performance_scaling/mod.rs (#2145).

use super::*;
use super::{MIN_MEASURABLE_US, QUADRATIC_THRESHOLD};

// ============================================================
// Test 6: Broadcast cap bounds quadratic E-matching
// ============================================================

/// After BROADCAST_INSTANCE_CAP (30), broadcast assumptions are added as
/// ground formulas (no quantification). This test verifies the cap is
/// enforced: verification still succeeds with many broadcasts.
#[test]
fn test_broadcast_cap_prevents_unbounded_instantiation() {
    let small = 10;
    let large = 50;

    let t_small = measure_median(|| time_verify_n_broadcasts(small), 3);
    let t_large = measure_median(|| time_verify_n_broadcasts(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Broadcast-cap scaling appears worse than linear: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x. \
         The ground-instance cap may not be bounding quantified broadcasts.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

fn time_verify_n_broadcasts(n: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound", "x > 0"));

    // Add N broadcast assumptions. Above BROADCAST_INSTANCE_CAP (30), they
    // degrade to ground assertions (no quantification).
    // Body "x == x" is a tautology — avoids vacuous truth from "forall x: x > 0" (#2258).
    for i in 0..n {
        let mut obligation = ProofObligation::broadcast_assume(format!("bc_{}", i), "x == x");
        obligation = obligation.with_bound_vars(vec!["x".to_string()]);
        ctx.obligations.push(obligation);
    }

    ctx.push_obligation(ProofObligation::assert("check", "x >= 0"));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    // broadcast_cap_hit is LOW risk (conservative — removes forall quantification,
    // giving solver LESS info). No demotion occurs. The assertion should still
    // verify because the base assumption x > 0 implies x >= 0 regardless of
    // broadcasts. Risk tier corrected from HIGH to LOW in #2224 audit.
    expect_verified(
        &result,
        "Broadcast cap is conservative (LOW risk), no demotion",
    );

    elapsed
}

// ============================================================
// Test 7: Combined assertion × variable scaling (the hot path)
// ============================================================

/// The full verification cost is O(A * (V + K + B)). For A assertions,
/// V variables, K assumptions: increasing both A and V by 2x should
/// increase time by ~4x (linear × linear), not ~16x (quadratic × quadratic).
#[test]
fn test_combined_assertions_variables_scaling() {
    let small_a = 3;
    let small_v = 3;
    let large_a = 12;
    let large_v = 12;

    let t_small = measure_median(|| time_combined_scaling(small_a, small_v), 3);
    let t_large = measure_median(|| time_combined_scaling(large_a, large_v), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    // Expect roughly (4 * 4) = 16x because both dimensions scaled 4x
    // and cost is O(A * V). Threshold at 100x to catch cubic/quartic.
    assert!(
        ratio < 100.0,
        "Combined A×V scaling appears worse than quadratic: \
         T({}×{})={}μs, T({}×{})={}μs, ratio={:.1}x (expected ≤16x for O(AV))",
        small_a,
        small_v,
        t_small,
        large_a,
        large_v,
        t_large,
        ratio,
    );
}

fn time_combined_scaling(n_assertions: usize, n_vars: usize) -> u128 {
    let mut ctx = VerificationContext::new();

    for i in 0..n_vars {
        ctx.declare_var_typed(
            &format!("v{}", i),
            crate::ir::TrustVcType::parse_or_opaque("i32"),
        );
    }
    ctx.push_obligation(ProofObligation::assume("bound", "v0 > 0"));

    for i in 0..n_assertions {
        ctx.push_obligation(ProofObligation::assert(format!("id_{}", i), "v0 + 0 == v0"));
    }

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(&result, "Combined scaling test failed");

    elapsed
}

// ============================================================
// Test 8: infer_int_width_from_types cost per call
// ============================================================

/// `infer_int_width_from_types` allocates a HashMap per call. This test
/// verifies the cost scales linearly with type count, not worse.
#[test]
fn test_infer_int_width_scales_linearly() {
    use crate::encoder::types::infer_int_width_from_types;
    use crate::ir::TrustVcType;

    let small = 20;
    let large = 80;

    let types_small: Vec<TrustVcType> =
        (0..small).map(|_| TrustVcType::Int { width: 32 }).collect();

    let types_large: Vec<TrustVcType> =
        (0..large).map(|_| TrustVcType::Int { width: 32 }).collect();

    let t_small = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..10_000 {
                let _ = infer_int_width_from_types(types_small.iter());
            }
            start.elapsed().as_micros()
        },
        3,
    );

    let t_large = measure_median(
        || {
            let start = std::time::Instant::now();
            for _ in 0..10_000 {
                let _ = infer_int_width_from_types(types_large.iter());
            }
            start.elapsed().as_micros()
        },
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "infer_int_width scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

// ============================================================
// Test 9: Invariant cascade scaling
// ============================================================

/// The invariant verification loop (typed.rs) accumulates
/// `verified_invariant_obligations` — invariant i re-encodes 0..i-1
/// prior invariants as assumptions. This creates O(I²/2) assumption
/// encodings across all invariants. For small I (1-5) this is
/// negligible; we test that it doesn't blow up for larger I.
///
/// Each invariant also triggers an inductive step, which creates an
/// additional frame-condition encoder. Total encoder setups: 2*I
/// (base + inductive per invariant).
///
/// The test uses u32 variables so `x >= 0` invariants are tautological
/// for both base case and inductive step (u32 is always >= 0).
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
    // scale = large/small = 4x, but this test uses cubic_threshold directly
    // Expected: O(I² * (V+K+B)). With V, K, B fixed, this is O(I²).
    // So T(4N)/T(N) ≈ 16x is acceptable (quadratic), but > 64x (cubic) is not.
    let cubic_threshold = 64.0;

    assert!(
        ratio < cubic_threshold,
        "Invariant cascade scaling appears cubic or worse: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (expected ≤{:.0}x for \
         quadratic). The verified_invariant_obligations cascade in \
         verify_typed may have regressed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        cubic_threshold,
    );
}

fn time_verify_n_invariants(n: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    // Use u32 so invariants are tautological (always >= 0).
    for i in 0..n {
        ctx.declare_var_typed(
            &format!("v{}", i),
            crate::ir::TrustVcType::parse_or_opaque("u32"),
        );
    }
    ctx.push_obligation(ProofObligation::assume("init", "v0 == 0"));

    for i in 0..n {
        ctx.obligations
            .push(crate::vc::ProofObligation::loop_invariant(
                format!("inv_{}", i),
                format!("v{} >= 0", i),
            ));
    }

    ctx.push_obligation(ProofObligation::assert("check", "v0 >= 0"));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    // With u32 variables, `v >= 0` is tautological — always verifies.
    expect_verified(&result, "Invariant cascade test setup failed at n={}");

    elapsed
}

// ============================================================
// Test 10: Literal count scaling (infer_int_width per-literal)
// ============================================================

/// Each unsuffixed Int{32} literal calls `infer_int_width()` which scans
/// all variable types. With L literals and V variables, total cost is
/// O(L*V). This test verifies that scaling in L (fixed V) stays linear,
/// catching any regression to O(L²) from e.g. re-computing variable
/// context per literal-pair instead of per literal.
///
/// Performance note: `infer_int_width` could be cached once per
/// AstExpressionParser (var_types is immutable during encoding) to
/// reduce O(L*V) to O(V). See ir_encoder/mod.rs:112.
#[test]
fn test_literal_count_scaling_linear_in_l() {
    let small_l = 5;
    let large_l = 20;
    let n_vars = 10;

    let t_small = measure_median(|| time_verify_n_literals(small_l, n_vars), 3);
    let t_large = measure_median(|| time_verify_n_literals(large_l, n_vars), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_l as f64 / small_l as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Literal-count scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x. \
         infer_int_width is called per default-typed literal — \
         cache it on AstExpressionParser to reduce O(L*V) to O(V).",
        small_l,
        t_small,
        large_l,
        t_large,
        ratio,
        normalized,
    );
}

fn time_verify_n_literals(n_literals: usize, n_vars: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    for i in 0..n_vars {
        ctx.declare_var_typed(
            &format!("v{}", i),
            crate::ir::TrustVcType::parse_or_opaque("i32"),
        );
    }
    ctx.push_obligation(ProofObligation::assume("bound", "v0 > 0"));

    // Build assertion: v0 + 1 + 2 + ... + L == v0 + sum(1..=L)
    // Each literal is unsuffixed Int{32}, hitting infer_int_width.
    let sum: i64 = (1..=n_literals as i64).sum();
    let additions: String = (1..=n_literals)
        .map(|i| format!(" + {}", i))
        .collect::<String>();
    let assertion = format!("v0{} == v0 + {}", additions, sum);
    ctx.push_obligation(ProofObligation::assert("literal_scaling", &assertion));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(&result, "Literal scaling test failed at L={}, V={}");
    elapsed
}
