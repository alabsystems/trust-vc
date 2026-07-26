// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn ap_first_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a0", i32_ty());
    ctx.declare_var_typed("a1", i32_ty());
    ctx.declare_var_typed("a2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 2"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 + 3"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 + 3"));
    ctx.push_obligation(ProofObligation::assert("a2_is_8", "a2 == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AP(2, d=3): 2, 5, 8");
}

#[test]
fn ap_constant_difference() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 10"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 + 5"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 + 5"));
    ctx.push_obligation(ProofObligation::assume("a3_def", "a3 == a2 + 5"));
    ctx.push_obligation(ProofObligation::assert(
        "constant_diff",
        "a1 - a0 == a2 - a1 && a2 - a1 == a3 - a2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "constant difference d=5");
}

#[test]
fn ap_sum_four_terms() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "sum"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 1"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 + 2"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 + 2"));
    ctx.push_obligation(ProofObligation::assume("a3_def", "a3 == a2 + 2"));
    ctx.push_obligation(ProofObligation::assume(
        "sum_def",
        "sum == a0 + a1 + a2 + a3",
    ));
    ctx.push_obligation(ProofObligation::assert("sum_is_16", "sum == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 + 3 + 5 + 7 = 16");
}

#[test]
fn ap_negative_difference() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 20"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 - 4"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 - 4"));
    ctx.push_obligation(ProofObligation::assert("a2_is_12", "a2 == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AP(20, d=-4): 20, 16, 12");
}

#[test]
fn ap_middle_is_average() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "sum", "avg"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 4"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 + 6"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 + 6"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a0 + a2"));
    ctx.push_obligation(ProofObligation::assume("avg_def", "avg == sum / 2"));
    ctx.push_obligation(ProofObligation::assert("mid_is_avg", "avg == a1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "middle term equals average of endpoints");
}

#[test]
fn ap_five_terms() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "a4"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 0"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 + 10"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 + 10"));
    ctx.push_obligation(ProofObligation::assume("a3_def", "a3 == a2 + 10"));
    ctx.push_obligation(ProofObligation::assume("a4_def", "a4 == a3 + 10"));
    ctx.push_obligation(ProofObligation::assert("a4_is_40", "a4 == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AP(0, d=10): 0, 10, 20, 30, 40");
}

#[test]
fn ap_strictly_increasing() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 5"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 + 3"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 + 3"));
    ctx.push_obligation(ProofObligation::assume("a3_def", "a3 == a2 + 3"));
    ctx.push_obligation(ProofObligation::assert(
        "increasing",
        "a0 < a1 && a1 < a2 && a2 < a3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AP with d>0 is strictly increasing");
}

#[test]
fn ap_first_last_sum() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 1"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 + 3"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 + 3"));
    ctx.push_obligation(ProofObligation::assume("a3_def", "a3 == a2 + 3"));
    ctx.push_obligation(ProofObligation::assert("first_last", "a0 + a3 == a1 + a2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "first+last = second+third in AP");
}

#[test]
fn ap_zero_difference() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 42"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1"));
    ctx.push_obligation(ProofObligation::assert("all_equal", "a0 == a1 && a1 == a2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AP with d=0 is constant");
}

#[test]
fn ap_alternating_sum() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "alt_sum"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 2"));
    ctx.push_obligation(ProofObligation::assume("a1_def", "a1 == a0 + 3"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == a1 + 3"));
    ctx.push_obligation(ProofObligation::assume("a3_def", "a3 == a2 + 3"));
    ctx.push_obligation(ProofObligation::assume(
        "alt_sum_def",
        "alt_sum == a0 - a1 + a2 - a3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "alt_sum_is_neg6",
        "alt_sum == 0 - 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2 - 5 + 8 - 11 = -6");
}
