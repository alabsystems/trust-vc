// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn fold_sum_three_elements() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "acc0", "acc1", "acc2", "acc3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 30"));
    ctx.push_obligation(ProofObligation::assume("acc0_val", "acc0 == 0"));
    ctx.push_obligation(ProofObligation::assume("acc1_def", "acc1 == acc0 + a"));
    ctx.push_obligation(ProofObligation::assume("acc2_def", "acc2 == acc1 + b"));
    ctx.push_obligation(ProofObligation::assume("acc3_def", "acc3 == acc2 + c"));
    ctx.push_obligation(ProofObligation::assert("sum_60", "acc3 == 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fold(+, 0, [10,20,30]) = 60");
}

#[test]
fn fold_product_three_elements() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "acc0", "acc1", "acc2", "acc3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 4"));
    ctx.push_obligation(ProofObligation::assume("acc0_val", "acc0 == 1"));
    ctx.push_obligation(ProofObligation::assume("acc1_def", "acc1 == acc0 * a"));
    ctx.push_obligation(ProofObligation::assume("acc2_def", "acc2 == acc1 * b"));
    ctx.push_obligation(ProofObligation::assume("acc3_def", "acc3 == acc2 * c"));
    ctx.push_obligation(ProofObligation::assert("product_24", "acc3 == 24"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "fold(*, 1, [2,3,4]) = 24");
}

#[test]
fn scan_running_sum() {
    // scan produces intermediate accumulators
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "s0", "s1", "s2", "s3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume("s0_val", "s0 == 0"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == s0 + a"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + b"));
    ctx.push_obligation(ProofObligation::assume("s3_def", "s3 == s2 + c"));
    ctx.push_obligation(ProofObligation::assert("s1_is_1", "s1 == 1"));
    ctx.push_obligation(ProofObligation::assert("s2_is_3", "s2 == 3"));
    ctx.push_obligation(ProofObligation::assert("s3_is_6", "s3 == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scan(+, 0, [1,2,3]) = [1,3,6]");
}

#[test]
fn reduce_max_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "m1", "m2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "m1_def",
        "m1 == if a >= b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m2_def",
        "m2 == if m1 >= c { m1 } else { c }",
    ));
    ctx.push_obligation(ProofObligation::assert("max_is_9", "m2 == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reduce(max, [5,9,3]) = 9");
}

#[test]
fn reduce_min_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "m1", "m2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "m1_def",
        "m1 == if a <= b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m2_def",
        "m2 == if m1 <= c { m1 } else { c }",
    ));
    ctx.push_obligation(ProofObligation::assert("min_is_3", "m2 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reduce(min, [5,9,3]) = 3");
}

#[test]
fn map_increment_elements() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "ma", "mb", "mc"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 30"));
    ctx.push_obligation(ProofObligation::assume("ma_def", "ma == a + 1"));
    ctx.push_obligation(ProofObligation::assume("mb_def", "mb == b + 1"));
    ctx.push_obligation(ProofObligation::assume("mc_def", "mc == c + 1"));
    ctx.push_obligation(ProofObligation::assert("ma_11", "ma == 11"));
    ctx.push_obligation(ProofObligation::assert("mb_21", "mb == 21"));
    ctx.push_obligation(ProofObligation::assert("mc_31", "mc == 31"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "map(+1, [10,20,30]) = [11,21,31]");
}

#[test]
fn filter_positive_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0 - 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 7"));
    // Count elements > 0
    ctx.push_obligation(ProofObligation::assume(
        "count_def",
        "count == (if a > 0 { 1 } else { 0 }) + (if b > 0 { 1 } else { 0 }) + (if c > 0 { 1 } else { 0 })",
    ));
    ctx.push_obligation(ProofObligation::assert("two_positive", "count == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filter(>0, [5,-3,7]).count() = 2");
}

#[test]
fn zip_add_pairs() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "b0", "b1", "c0", "c1"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a0_val", "a0 == 1"));
    ctx.push_obligation(ProofObligation::assume("a1_val", "a1 == 2"));
    ctx.push_obligation(ProofObligation::assume("b0_val", "b0 == 10"));
    ctx.push_obligation(ProofObligation::assume("b1_val", "b1 == 20"));
    ctx.push_obligation(ProofObligation::assume("c0_def", "c0 == a0 + b0"));
    ctx.push_obligation(ProofObligation::assume("c1_def", "c1 == a1 + b1"));
    ctx.push_obligation(ProofObligation::assert("c0_11", "c0 == 11"));
    ctx.push_obligation(ProofObligation::assert("c1_22", "c1 == 22"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zip_add([1,2], [10,20]) = [11,22]");
}

#[test]
fn enumerate_index_value_pairs() {
    let mut ctx = VerificationContext::new();
    for v in &["v0", "v1", "v2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    for v in &["i0", "i1", "i2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v0_val", "v0 == 100"));
    ctx.push_obligation(ProofObligation::assume("v1_val", "v1 == 200"));
    ctx.push_obligation(ProofObligation::assume("v2_val", "v2 == 300"));
    ctx.push_obligation(ProofObligation::assume("i0_def", "i0 == 0"));
    ctx.push_obligation(ProofObligation::assume("i1_def", "i1 == 1"));
    ctx.push_obligation(ProofObligation::assume("i2_def", "i2 == 2"));
    ctx.push_obligation(ProofObligation::assert("idx_seq", "i0 < i1 && i1 < i2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "enumerate indices are sequential");
}

#[test]
fn fold_count_matching() {
    // fold to count elements equal to target
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "target"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.declare_var_typed("count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume("target_val", "target == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "count_def",
        "count == (if a == target { 1 } else { 0 }) + (if b == target { 1 } else { 0 }) + (if c == target { 1 } else { 0 })",
    ));
    ctx.push_obligation(ProofObligation::assert("two_match", "count == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "count_matching(5, [5,3,5]) = 2");
}
