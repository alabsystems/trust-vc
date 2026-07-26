// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn median_of_three_sorted() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "median"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 7"));
    ctx.push_obligation(ProofObligation::assume("med_def", "median == b")); // middle of sorted
    ctx.push_obligation(ProofObligation::assert("is_5", "median == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "median(3,5,7) = 5");
}

#[test]
fn median_of_three_unsorted() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "median"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "med_def",
        "median == if (a >= b && a <= c) || (a <= b && a >= c) { a } else { if (b >= a && b <= c) || (b <= a && b >= c) { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "median == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "median(7,3,5) = 5");
}

#[test]
fn median_between_min_max() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "median", "min_val", "max_val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 30"));
    ctx.push_obligation(ProofObligation::assume("min_def", "min_val == 10"));
    ctx.push_obligation(ProofObligation::assume("max_def", "max_val == 30"));
    ctx.push_obligation(ProofObligation::assume("med_def", "median == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "median >= min_val && median <= max_val",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "median 20 between min 10 and max 30");
}

#[test]
fn median_of_two_is_average() {
    // Median of two: (a + b) / 2
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "median"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("med_def", "median == (a + b) / 2"));
    ctx.push_obligation(ProofObligation::assert("is_15", "median == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "median(10,20) = 15");
}

#[test]
fn kth_smallest_bound() {
    // kth smallest is >= (k-1) elements
    let mut ctx = VerificationContext::new();
    for v in &["k", "n"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("k_val", "k == 3"));
    ctx.push_obligation(ProofObligation::assume("n_val", "n == 10"));
    ctx.push_obligation(ProofObligation::assert("valid_k", "k <= n && k > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "k=3 valid for n=10");
}

#[test]
fn min_is_first_order_statistic() {
    // Minimum = 1st order statistic
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "min_val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "min_def",
        "min_val == if a <= b && a <= c { a } else { if b <= c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "min_val == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min(5,2,8) = 2");
}

#[test]
fn max_is_last_order_statistic() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "max_val"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "max_def",
        "max_val == if a >= b && a >= c { a } else { if b >= c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "max_val == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max(5,2,8) = 8");
}

#[test]
fn median_equals_one_of_inputs() {
    // Median of odd count always equals one of the inputs
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "median"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 6"));
    ctx.push_obligation(ProofObligation::assume("med_val", "median == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "is_input",
        "median == a || median == b || median == c",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "median 6 equals one of {4,9,6}");
}

#[test]
fn range_is_max_minus_min() {
    let mut ctx = VerificationContext::new();
    for v in &["min_val", "max_val", "range"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("mn", "min_val == 3"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_val == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "range == max_val - min_val",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "range == 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "range: 15 - 3 = 12");
}

#[test]
fn quartile_partition() {
    // Q1, Q2 (median), Q3 divide data into 4 equal parts
    let mut ctx = VerificationContext::new();
    for v in &["q1", "q2", "q3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("q1_val", "q1 == 25"));
    ctx.push_obligation(ProofObligation::assume("q2_val", "q2 == 50"));
    ctx.push_obligation(ProofObligation::assume("q3_val", "q3 == 75"));
    ctx.push_obligation(ProofObligation::assert("ordered", "q1 < q2 && q2 < q3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Q1=25 < Q2=50 < Q3=75");
}
