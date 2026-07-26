// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn two_element_sort() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "lo", "hi"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lo == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hi == if a > b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("sorted", "lo <= hi"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min/max sorts two elements");
}

#[test]
fn sorted_pair_preserves_elements() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "lo", "hi"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lo == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hi == if a > b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("sum_preserved", "lo + hi == a + b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sorting preserves sum (hence elements)");
}

#[test]
fn already_sorted() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "lo", "hi"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lo == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hi == if a > b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("identity", "lo == a && hi == b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "already sorted pair is unchanged");
}

#[test]
fn three_element_min() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "m"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "m == if a < b { if a < c { a } else { c } } else { if b < c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_min", "m == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min(5, 2, 8) = 2");
}

#[test]
fn three_element_max() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "m"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "m == if a > b { if a > c { a } else { c } } else { if b > c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_max", "m == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max(5, 2, 8) = 8");
}

#[test]
fn sort_three_first_is_min() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "s1", "s2", "s3"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 2"));
    // Bubble sort: compare and swap adjacent pairs
    // Step 1: sort (a,b)
    ctx.push_obligation(ProofObligation::assume(
        "s1_def",
        "s1 == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s2_def",
        "s2 == if a > b { a } else { b }",
    ));
    // Step 2: sort (s2,c) to get s2,s3
    ctx.push_obligation(ProofObligation::assume(
        "s3_def",
        "s3 == if s2 > c { s2 } else { c }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "first_is_min",
        "s1 <= s2 && s1 <= c",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "after sorting, s1 is min of {3,1,2}");
}

#[test]
fn equal_elements_sorted() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "lo", "hi"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lo == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hi == if a > b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert("all_equal", "lo == 5 && hi == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equal elements remain equal after sort");
}

#[test]
fn negative_elements_sorted() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "lo", "hi"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0 - 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0 - 7"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lo == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hi == if a > b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sorted_neg",
        "lo == 0 - 7 && hi == 0 - 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sort(-3, -7) = (-7, -3)");
}

#[test]
fn sort_idempotent() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "lo", "hi", "lo2", "hi2"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 9"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    // First sort
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lo == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hi == if a > b { a } else { b }",
    ));
    // Second sort on already-sorted
    ctx.push_obligation(ProofObligation::assume(
        "lo2_def",
        "lo2 == if lo < hi { lo } else { hi }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi2_def",
        "hi2 == if lo > hi { lo } else { hi }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "idempotent",
        "lo2 == lo && hi2 == hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sorting twice is same as sorting once");
}

#[test]
fn median_of_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "med"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "med_def",
        "med == if a >= b && a <= c { a } else { if a >= c && a <= b { a } else { if b >= a && b <= c { b } else { if b >= c && b <= a { b } else { c } } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_median", "med == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "median(7, 3, 5) = 5");
}
