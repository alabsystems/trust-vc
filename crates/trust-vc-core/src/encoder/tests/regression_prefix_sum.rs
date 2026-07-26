// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn prefix_sum_single() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a0", i32_ty());
    ctx.declare_var_typed("s0", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a0_bound",
        "a0 >= -10000 && a0 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s0_bound",
        "s0 >= -10000 && s0 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 5"));
    ctx.push_obligation(ProofObligation::assume("s0_def", "s0 == a0"));
    ctx.push_obligation(ProofObligation::assert("s0_is_5", "s0 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prefix sum of a single element");
}

#[test]
fn prefix_sum_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a0", i32_ty());
    ctx.declare_var_typed("a1", i32_ty());
    ctx.declare_var_typed("s0", i32_ty());
    ctx.declare_var_typed("s1", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a0_bound",
        "a0 >= -10000 && a0 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "a1_bound",
        "a1 >= -10000 && a1 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s0_bound",
        "s0 >= -10000 && s0 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s1_bound",
        "s1 >= -10000 && s1 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 3"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 7"));
    ctx.push_obligation(ProofObligation::assume("s0_def", "s0 == a0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + a1"));
    ctx.push_obligation(ProofObligation::assert("s1_is_10", "s1 == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prefix sum of two elements");
}

#[test]
fn prefix_sum_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "s0", "s1", "s2"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 1"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 2"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 3"));
    ctx.push_obligation(ProofObligation::assume("s0_def", "s0 == a0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + a1"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + a2"));
    ctx.push_obligation(ProofObligation::assert("s2_is_6", "s2 == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prefix sum of three elements");
}

#[test]
fn prefix_sum_four() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "s0", "s1", "s2", "s3"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 10"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 20"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 30"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 40"));
    ctx.push_obligation(ProofObligation::assume("s0_def", "s0 == a0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + a1"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + a2"));
    ctx.push_obligation(ProofObligation::assume("s3_def", "s3 == s2 + a3"));
    ctx.push_obligation(ProofObligation::assert("s3_is_100", "s3 == 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prefix sum of four elements");
}

#[test]
fn prefix_sum_monotone() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "s0", "s1", "s2"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 1"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 2"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 3"));
    ctx.push_obligation(ProofObligation::assume("s0_def", "s0 == a0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + a1"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + a2"));
    ctx.push_obligation(ProofObligation::assert("monotone", "s0 <= s1 && s1 <= s2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prefix sums of positive values are monotone");
}

#[test]
fn prefix_sum_with_negatives() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "s0", "s1", "s2"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 5"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == -3"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 2"));
    ctx.push_obligation(ProofObligation::assume("s0_def", "s0 == a0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + a1"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + a2"));
    ctx.push_obligation(ProofObligation::assert("s2_is_4", "s2 == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "prefix sum handles negative elements");
}

#[test]
fn prefix_max_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a0", i32_ty());
    ctx.declare_var_typed("a1", i32_ty());
    ctx.declare_var_typed("m0", i32_ty());
    ctx.declare_var_typed("m1", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 3"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 7"));
    ctx.push_obligation(ProofObligation::assume("m0_def", "m0 == a0"));
    ctx.push_obligation(ProofObligation::assume(
        "m1_def",
        "m1 == if a1 > m0 { a1 } else { m0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("m1_is_7", "m1 == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "running max of [3, 7] is 7");
}

#[test]
fn prefix_max_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a0", i32_ty());
    ctx.declare_var_typed("a1", i32_ty());
    ctx.declare_var_typed("a2", i32_ty());
    ctx.declare_var_typed("m0", i32_ty());
    ctx.declare_var_typed("m1", i32_ty());
    ctx.declare_var_typed("m2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 3"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 7"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 5"));
    ctx.push_obligation(ProofObligation::assume("m0_def", "m0 == a0"));
    ctx.push_obligation(ProofObligation::assume(
        "m1_def",
        "m1 == if a1 > m0 { a1 } else { m0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m2_def",
        "m2 == if a2 > m1 { a2 } else { m1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("m2_is_7", "m2 == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "running max of [3, 7, 5] is 7");
}

#[test]
fn running_average_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a0", i32_ty());
    ctx.declare_var_typed("a1", i32_ty());
    ctx.declare_var_typed("sum", i32_ty());
    ctx.declare_var_typed("avg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "a0_bound",
        "a0 >= -10000 && a0 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "a1_bound",
        "a1 >= -10000 && a1 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sum_bound",
        "sum >= -10000 && sum <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "avg_bound",
        "avg >= -10000 && avg <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 10"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 20"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a0 + a1"));
    ctx.push_obligation(ProofObligation::assume("avg_def", "avg == sum / 2"));
    ctx.push_obligation(ProofObligation::assert("avg_is_15", "avg == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "average of 10 and 20 is 15");
}

#[test]
fn prefix_sum_difference() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "s0", "s1", "s2"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 5"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 3"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 7"));
    ctx.push_obligation(ProofObligation::assume("s0_def", "s0 == a0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + a1"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + a2"));
    ctx.push_obligation(ProofObligation::assert("diff_is_a2", "s2 - s1 == a2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "difference of consecutive prefix sums is the element",
    );
}
