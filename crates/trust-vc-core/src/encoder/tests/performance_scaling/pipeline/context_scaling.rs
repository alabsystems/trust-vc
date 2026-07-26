// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;
use super::super::{MIN_MEASURABLE_US, QUADRATIC_THRESHOLD};

// ============================================================
// Test 1: Assertion count scaling
// ============================================================

/// Verification time should scale roughly linearly with assertion count
/// when variable count and assumption count are held constant.
///
/// The fresh-encoder-per-assertion strategy creates a new solver per
/// assertion. With V variables and K assumptions, each assertion costs
/// O(V + K). Total should be O(A * (V + K)), i.e., linear in A for
/// fixed V, K.
#[test]
fn test_scaling_assertion_count_linear() {
    let small = 5;
    let large = 20;

    let t_small = measure_median(|| time_verify_n_assertions(small), 3);
    let t_large = measure_median(|| time_verify_n_assertions(large), 3);

    if t_small < MIN_MEASURABLE_US {
        // Too fast to measure — pass vacuously
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64; // 4x
    let normalized = ratio / scale; // Should be ~1 for linear, ~4 for quadratic

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Assertion scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (expected ~{:.0}x for linear, \
         got {:.1}x normalized). Fresh-encoder-per-assertion may have regressed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        scale,
        normalized,
    );
}

fn time_verify_n_assertions(n: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    // Fixed set of variables
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("bound", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("bound2", "y > 0"));

    // N assertions, all trivially true
    for i in 0..n {
        ctx.push_obligation(ProofObligation::assert(
            format!("identity_{}", i),
            "x + 0 == x",
        ));
    }

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(&result, "Scaling test setup failed");

    elapsed
}

/// Stress regression for #949: large functions with 100+ assertions should
/// still verify through the full fresh-encoder-per-assertion pipeline.
///
/// The smaller ratio test above catches asymptotic regressions; this test
/// guards the concrete large-batch case from the issue by making TrustVc prove
/// 128 independent obligations in one context without falling into Unknown or
/// fail-closed errors.
#[test]
fn test_large_assertion_batch_stress_verifies() {
    const ASSERTION_COUNT: usize = 128;
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::requires("x_fixed", "x == 7"));
    ctx.push_obligation(ProofObligation::requires("y_fixed", "y == 11"));

    for i in 0..ASSERTION_COUNT {
        ctx.push_obligation(ProofObligation::assert(
            format!("sum_identity_{i}"),
            "x + y == 18",
        ));
    }

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "128-assertion batch should verify without timeout or fail-closed errors",
    );
}

/// Stress regression for #949: a realistic function has diverse assertion types,
/// not 128 copies of the same formula. This test mixes arithmetic comparisons,
/// equalities, and transitive chains to ensure the fresh-encoder-per-assertion
/// pipeline handles heterogeneous obligations without fail-closed errors.
#[test]
fn test_diverse_assertion_batch_stress_verifies() {
    const ASSERTION_COUNT: usize = 64;
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::requires("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::requires("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::requires("c_val", "c == 30"));

    for i in 0..ASSERTION_COUNT {
        let (name, cond) = match i % 4 {
            0 => (format!("sum_eq_{i}"), "a + b + c == 60".to_string()),
            1 => (format!("order_{i}"), "a < b".to_string()),
            2 => (format!("transitivity_{i}"), "a < c".to_string()),
            _ => (format!("arith_{i}"), "b + c > a".to_string()),
        };
        ctx.push_obligation(ProofObligation::assert(name, cond));
    }

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "64 diverse assertions should verify without timeout or fail-closed errors",
    );
}

/// Stress regression for #949: assumption-heavy context. A chain of 64
/// assumptions (v0 == 0, v1 == v0 + 1, v2 == v1 + 1, ...) feeding a
/// single assertion (v63 == 63). The solver must use the entire chain
/// to prove the assertion. Tests that assumption encoding scales without
/// quadratic blowup when the assumption count dominates.
///
/// Uses u32 variables to avoid signed overflow counterexamples on additions.
#[test]
fn test_assumption_heavy_stress_verifies() {
    const CHAIN_LEN: usize = 64;
    let mut ctx = VerificationContext::new();

    // Declare all variables as u32 (avoids signed overflow on small additions).
    for i in 0..CHAIN_LEN {
        ctx.declare_var_typed(
            &format!("v{i}"),
            crate::ir::TrustVcType::parse_or_opaque("u32"),
        );
    }

    // Base case: v0 == 0.
    ctx.push_obligation(ProofObligation::requires("base", "v0 == 0"));

    // Chain: v_{i+1} == v_i + 1 for i in 0..63.
    // The solver must follow the entire chain to derive v63 == 63.
    for i in 0..(CHAIN_LEN - 1) {
        let next = i + 1;
        ctx.push_obligation(ProofObligation::requires(
            format!("chain_{i}"),
            format!("v{next} == v{i} + 1"),
        ));
    }

    // Assertion: v63 == 63. Requires all 64 chain links.
    let last = CHAIN_LEN - 1;
    ctx.push_obligation(ProofObligation::assert(
        "chain_result",
        format!("v{last} == {last}"),
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "64-link assumption chain should verify without timeout",
    );
}

// ============================================================
// Test 2: Variable count scaling (encoder setup cost)
// ============================================================

/// Encoder setup time should scale linearly with variable count.
///
/// `setup_from_context` declares all V variables (O(V)), then iterates
/// for broadcasts. The AstExpressionParser constructor iterates 3x over
/// variables (term_widths, collection_lengths, collection_meta_by_term).
/// Total per-encoder-setup should be O(V).
#[test]
fn test_scaling_variable_count_linear() {
    let small = 5;
    let large = 20;

    let t_small = measure_median(|| time_verify_n_variables(small), 3);
    let t_large = measure_median(|| time_verify_n_variables(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Variable scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (expected ~{:.0}x for linear, \
         got {:.1}x normalized). Encoder setup may have regressed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        scale,
        normalized,
    );
}

fn time_verify_n_variables(n: usize) -> u128 {
    let mut ctx = VerificationContext::new();

    // N variables
    for i in 0..n {
        ctx.declare_var_typed(
            &format!("v{}", i),
            crate::ir::TrustVcType::parse_or_opaque("i32"),
        );
    }

    // Always add v0 for assumptions/assertions to reference
    if n == 0 {
        ctx.declare_var_typed("v0", crate::ir::TrustVcType::parse_or_opaque("i32"));
    }
    ctx.push_obligation(ProofObligation::assume("bound", "v0 > 0"));
    ctx.push_obligation(ProofObligation::assert("check", "v0 >= 0"));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(&result, "Scaling test setup failed");

    elapsed
}

// ============================================================
// Test 3: Assumption count scaling
// ============================================================

/// Verification time should scale linearly with assumption count.
///
/// Each assumption is encoded once per assertion (fresh encoder strategy).
/// For A=1 assertion, K assumptions, the cost should be O(K).
#[test]
fn test_scaling_assumption_count_linear() {
    let small = 5;
    let large = 20;

    let t_small = measure_median(|| time_verify_n_assumptions(small), 3);
    let t_large = measure_median(|| time_verify_n_assumptions(large), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "Assumption scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x (expected ~{:.0}x for linear, \
         got {:.1}x normalized). Assumption encoding may have regressed.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        scale,
        normalized,
    );
}

fn time_verify_n_assumptions(n: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

    // N assumptions: x > -i (all compatible)
    for i in 0..n {
        ctx.push_obligation(ProofObligation::assume(
            format!("assume_{}", i),
            format!("x > {}", -(i as i64) - 100),
        ));
    }

    ctx.push_obligation(ProofObligation::assert("check", "x + 0 == x"));

    let start = std::time::Instant::now();
    let result = AYEncoder::verify(&ctx);
    let elapsed = start.elapsed().as_micros();

    expect_verified(&result, "Scaling test setup failed");

    elapsed
}
