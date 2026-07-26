// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn saturate_add_no_overflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("sum", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 50"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    ctx.push_obligation(ProofObligation::assert("fits", "sum == 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 + 50 = 150 (no saturation needed)");
}

#[test]
fn clamp_to_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("max_val", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 200"));
    ctx.push_obligation(ProofObligation::assume("max_val_val", "max_val == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x > max_val { max_val } else { x }",
    ));
    ctx.push_obligation(ProofObligation::assert("clamped", "result == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(200, max=100) = 100");
}

#[test]
fn clamp_to_min() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("min_val", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 50"));
    ctx.push_obligation(ProofObligation::assume("min_val_val", "min_val == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x < min_val { min_val } else { x }",
    ));
    ctx.push_obligation(ProofObligation::assert("clamped", "result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(-50, min=0) = 0");
}

#[test]
fn clamp_both_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "lo", "hi", "result"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 50"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 10"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x < lo { lo } else { if x > hi { hi } else { x } }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "result >= lo && result <= hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(50, 10, 100) in [10, 100]");
}

#[test]
fn saturate_sub_no_underflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("result", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if a >= b { a - b } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("no_underflow", "result == 70"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "saturating_sub(100, 30) = 70");
}

#[test]
fn saturate_sub_underflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("result", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if a >= b { a - b } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("saturated", "result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "saturating_sub(10, 50) = 0");
}

#[test]
fn normalize_to_unit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x > 0 { 1 } else { if x < 0 { 0 - 1 } else { 0 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("unit", "result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "normalize(42) = 1");
}

#[test]
fn threshold_filter() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("threshold", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assume("threshold_val", "threshold == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x >= threshold { x } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("filtered", "result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "threshold_filter(3, threshold=5) = 0 (below threshold)",
    );
}

#[test]
fn dead_zone() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "lo", "hi", "result"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 2"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0 - 5"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x > lo && x < hi { 0 } else { x }",
    ));
    ctx.push_obligation(ProofObligation::assert("zeroed", "result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dead_zone(2, -5, 5) = 0 (in dead zone)");
}

#[test]
fn quantize_to_step() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "step", "result"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 17"));
    ctx.push_obligation(ProofObligation::assume("step_val", "step == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == (x / step) * step",
    ));
    ctx.push_obligation(ProofObligation::assert("quantized", "result == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "quantize(17, step=5) = 15");
}
