// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn running_sum_four() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "acc0", "acc1", "acc2", "acc3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 1"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 2"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 3"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 4"));
    ctx.push_obligation(ProofObligation::assume("acc0_def", "acc0 == a0"));
    ctx.push_obligation(ProofObligation::assume("acc1_def", "acc1 == acc0 + a1"));
    ctx.push_obligation(ProofObligation::assume("acc2_def", "acc2 == acc1 + a2"));
    ctx.push_obligation(ProofObligation::assume("acc3_def", "acc3 == acc2 + a3"));
    ctx.push_obligation(ProofObligation::assert("sum_is_10", "acc3 == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "running sum of [1,2,3,4] = 10");
}

#[test]
fn running_min_four() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "min0", "min1", "min2", "min3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 5"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 2"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 8"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 1"));
    ctx.push_obligation(ProofObligation::assume("min0_def", "min0 == a0"));
    ctx.push_obligation(ProofObligation::assume(
        "min1_def",
        "min1 == if a1 < min0 { a1 } else { min0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "min2_def",
        "min2 == if a2 < min1 { a2 } else { min1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "min3_def",
        "min3 == if a3 < min2 { a3 } else { min2 }",
    ));
    ctx.push_obligation(ProofObligation::assert("min_is_1", "min3 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "running min of [5,2,8,1] = 1");
}

#[test]
fn running_max_four() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "max0", "max1", "max2", "max3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 3"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 7"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 2"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 9"));
    ctx.push_obligation(ProofObligation::assume("max0_def", "max0 == a0"));
    ctx.push_obligation(ProofObligation::assume(
        "max1_def",
        "max1 == if a1 > max0 { a1 } else { max0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "max2_def",
        "max2 == if a2 > max1 { a2 } else { max1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "max3_def",
        "max3 == if a3 > max2 { a3 } else { max2 }",
    ));
    ctx.push_obligation(ProofObligation::assert("max_is_9", "max3 == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "running max of [3,7,2,9] = 9");
}

#[test]
fn count_positives() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "c0", "c1", "c2", "c3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 3"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 0 - 1"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 5"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 0 - 2"));
    ctx.push_obligation(ProofObligation::assume(
        "c0_def",
        "c0 == if a0 > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c1_def",
        "c1 == c0 + if a1 > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c2_def",
        "c2 == c1 + if a2 > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c3_def",
        "c3 == c2 + if a3 > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("count_is_2", "c3 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "count of positives in [3,-1,5,-2] = 2");
}

#[test]
fn running_sum_all_zeros() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "acc0", "acc1", "acc2", "acc3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 0"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 0"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 0"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 0"));
    ctx.push_obligation(ProofObligation::assume("acc0_def", "acc0 == a0"));
    ctx.push_obligation(ProofObligation::assume("acc1_def", "acc1 == acc0 + a1"));
    ctx.push_obligation(ProofObligation::assume("acc2_def", "acc2 == acc1 + a2"));
    ctx.push_obligation(ProofObligation::assume("acc3_def", "acc3 == acc2 + a3"));
    ctx.push_obligation(ProofObligation::assert("sum_is_0", "acc3 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "running sum of [0,0,0,0] = 0");
}

#[test]
fn running_sum_negative() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "acc0", "acc1", "acc2", "acc3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 0 - 1"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 0 - 2"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 0 - 3"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 0 - 4"));
    ctx.push_obligation(ProofObligation::assume("acc0_def", "acc0 == a0"));
    ctx.push_obligation(ProofObligation::assume("acc1_def", "acc1 == acc0 + a1"));
    ctx.push_obligation(ProofObligation::assume("acc2_def", "acc2 == acc1 + a2"));
    ctx.push_obligation(ProofObligation::assume("acc3_def", "acc3 == acc2 + a3"));
    ctx.push_obligation(ProofObligation::assert("sum_is_neg10", "acc3 == 0 - 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "running sum of [-1,-2,-3,-4] = -10");
}

#[test]
fn running_xor() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "x0", "x1", "x2", "x3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 5"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 3"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 6"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 4"));
    ctx.push_obligation(ProofObligation::assume("x0_def", "x0 == a0"));
    ctx.push_obligation(ProofObligation::assume("x1_def", "x1 == x0 ^ a1"));
    ctx.push_obligation(ProofObligation::assume("x2_def", "x2 == x1 ^ a2"));
    ctx.push_obligation(ProofObligation::assume("x3_def", "x3 == x2 ^ a3"));
    ctx.push_obligation(ProofObligation::assert("xor_is_4", "x3 == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "running XOR of [5,3,6,4] = 4");
}

#[test]
fn running_or() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "or0", "or1", "or2", "or3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 1"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 2"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 4"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 8"));
    ctx.push_obligation(ProofObligation::assume("or0_def", "or0 == a0"));
    ctx.push_obligation(ProofObligation::assume("or1_def", "or1 == or0 | a1"));
    ctx.push_obligation(ProofObligation::assume("or2_def", "or2 == or1 | a2"));
    ctx.push_obligation(ProofObligation::assume("or3_def", "or3 == or2 | a3"));
    ctx.push_obligation(ProofObligation::assert("or_is_15", "or3 == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "running OR of [1,2,4,8] = 15");
}

#[test]
fn accumulate_absolute_diff() {
    let mut ctx = VerificationContext::new();
    for v in &["x1", "y1", "x2", "y2", "d1", "d2", "total"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("x1_val", "x1 == 5"));
    ctx.push_obligation(ProofObligation::assume("y1_val", "y1 == 3"));
    ctx.push_obligation(ProofObligation::assume("x2_val", "x2 == 10"));
    ctx.push_obligation(ProofObligation::assume("y2_val", "y2 == 7"));
    ctx.push_obligation(ProofObligation::assume("d1_def", "d1 == x1 - y1"));
    ctx.push_obligation(ProofObligation::assume("d2_def", "d2 == x2 - y2"));
    ctx.push_obligation(ProofObligation::assume("total_def", "total == d1 + d2"));
    ctx.push_obligation(ProofObligation::assert("total_is_5", "total == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sum of diffs: (5-3)+(10-7) = 5");
}

#[test]
fn fold_max_of_abs() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "a0", "a1", "a2", "a3", "abs0", "abs1", "abs2", "abs3", "m0", "m1", "m2", "m3",
    ] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 3"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 0 - 5"));
    ctx.push_obligation(ProofObligation::assume("a2_val", "a2 == 2"));
    ctx.push_obligation(ProofObligation::assume("a3_val", "a3 == 0 - 1"));
    ctx.push_obligation(ProofObligation::assume(
        "abs0_def",
        "abs0 == if a0 >= 0 { a0 } else { 0 - a0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "abs1_def",
        "abs1 == if a1 >= 0 { a1 } else { 0 - a1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "abs2_def",
        "abs2 == if a2 >= 0 { a2 } else { 0 - a2 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "abs3_def",
        "abs3 == if a3 >= 0 { a3 } else { 0 - a3 }",
    ));
    ctx.push_obligation(ProofObligation::assume("m0_def", "m0 == abs0"));
    ctx.push_obligation(ProofObligation::assume(
        "m1_def",
        "m1 == if abs1 > m0 { abs1 } else { m0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m2_def",
        "m2 == if abs2 > m1 { abs2 } else { m1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m3_def",
        "m3 == if abs3 > m2 { abs3 } else { m2 }",
    ));
    ctx.push_obligation(ProofObligation::assert("max_abs_is_5", "m3 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max of abs values in [3,-5,2,-1] = 5");
}
