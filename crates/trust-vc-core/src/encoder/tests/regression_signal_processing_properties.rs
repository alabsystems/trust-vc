// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn moving_average_two_samples() {
    let mut ctx = VerificationContext::new();
    for v in &["s1", "s2", "avg"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s1_val", "s1 == 10"));
    ctx.push_obligation(ProofObligation::assume("s2_val", "s2 == 20"));
    ctx.push_obligation(ProofObligation::assume("avg_def", "avg == (s1 + s2) / 2"));
    ctx.push_obligation(ProofObligation::assert("is_15", "avg == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "moving avg(10, 20) = 15");
}

#[test]
fn gain_amplification() {
    // output = input * gain
    let mut ctx = VerificationContext::new();
    for v in &["input_signal", "gain", "output"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("is", "input_signal == 5"));
    ctx.push_obligation(ProofObligation::assume("g", "gain == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "output == input_signal * gain",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "output == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "gain: 5 * 3 = 15");
}

#[test]
fn clamp_to_range() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "low", "high", "clamped"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 150"));
    ctx.push_obligation(ProofObligation::assume("lo", "low == 0"));
    ctx.push_obligation(ProofObligation::assume("hi", "high == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "clamped == if val > high { high } else { if val < low { low } else { val } }",
    ));
    ctx.push_obligation(ProofObligation::assert("at_max", "clamped == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(150, 0, 100) = 100");
}

#[test]
fn difference_filter() {
    // y[n] = x[n] - x[n-1]
    let mut ctx = VerificationContext::new();
    for v in &["x_curr", "x_prev", "y"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("xc", "x_curr == 50"));
    ctx.push_obligation(ProofObligation::assume("xp", "x_prev == 30"));
    ctx.push_obligation(ProofObligation::assume("y_def", "y == x_curr - x_prev"));
    ctx.push_obligation(ProofObligation::assert("is_20", "y == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "difference filter: 50 - 30 = 20");
}

#[test]
fn accumulator_integration() {
    // Discrete integration: sum += sample
    let mut ctx = VerificationContext::new();
    for v in &["sum_prev", "sample", "sum_next"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sp", "sum_prev == 100"));
    ctx.push_obligation(ProofObligation::assume("s", "sample == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "sn_def",
        "sum_next == sum_prev + sample",
    ));
    ctx.push_obligation(ProofObligation::assert("is_125", "sum_next == 125"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accumulator: 100 + 25 = 125");
}

#[test]
fn peak_detection() {
    let mut ctx = VerificationContext::new();
    for v in &["prev", "curr", "next_sample"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("is_peak", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "prev == 5"));
    ctx.push_obligation(ProofObligation::assume("c", "curr == 10"));
    ctx.push_obligation(ProofObligation::assume("n", "next_sample == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "is_peak == if curr > prev && curr > next_sample { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("peak", "is_peak == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "peak: 10 > 5 and 10 > 3");
}

#[test]
fn downsample_by_two() {
    // Keep every other sample: output_len = input_len / 2
    let mut ctx = VerificationContext::new();
    for v in &["input_len", "factor", "output_len"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("il", "input_len == 100"));
    ctx.push_obligation(ProofObligation::assume("f", "factor == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ol_def",
        "output_len == input_len / factor",
    ));
    ctx.push_obligation(ProofObligation::assert("is_50", "output_len == 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "downsample by 2: 100 → 50 samples");
}

#[test]
fn threshold_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("signal", i32_ty());
    ctx.declare_var_typed("threshold", i32_ty());
    ctx.declare_var_typed("triggered", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "signal == 80"));
    ctx.push_obligation(ProofObligation::assume("t", "threshold == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "tr_def",
        "triggered == if signal >= threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "triggered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "signal 80 >= threshold 50 → triggered");
}

#[test]
fn windowed_energy() {
    // Energy = sum of squares (2 samples for simplicity)
    let mut ctx = VerificationContext::new();
    for v in &["s1", "s2", "e1", "e2", "energy"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s1_val", "s1 == 3"));
    ctx.push_obligation(ProofObligation::assume("s2_val", "s2 == 4"));
    ctx.push_obligation(ProofObligation::assume("e1_def", "e1 == s1 * s1"));
    ctx.push_obligation(ProofObligation::assume("e2_def", "e2 == s2 * s2"));
    ctx.push_obligation(ProofObligation::assume("en_def", "energy == e1 + e2"));
    // 9 + 16 = 25
    ctx.push_obligation(ProofObligation::assert("is_25", "energy == 25"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "energy: 3^2 + 4^2 = 25");
}

#[test]
fn zero_crossing_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("prev_sample", i32_ty());
    ctx.declare_var_typed("curr_sample", i32_ty());
    ctx.declare_var_typed("crossed_zero", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ps", "prev_sample == 0 - 5")); // -5
    ctx.push_obligation(ProofObligation::assume("cs", "curr_sample == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "cz_def",
        "crossed_zero == if (prev_sample < 0 && curr_sample >= 0) || (prev_sample >= 0 && curr_sample < 0) { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("crossed", "crossed_zero == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zero crossing: -5 → 3");
}
