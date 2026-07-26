// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn window_sum_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "sum"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b + c"));
    ctx.push_obligation(ProofObligation::assert("window_sum", "sum == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window sum [3,7,5] = 15");
}

#[test]
fn slide_window_add_remove() {
    let mut ctx = VerificationContext::new();
    for v in &["old_sum", "leaving", "entering", "new_sum"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    // Sliding: remove oldest, add newest
    ctx.push_obligation(ProofObligation::assume("old_sum_val", "old_sum == 15"));
    ctx.push_obligation(ProofObligation::assume("leaving_val", "leaving == 3"));
    ctx.push_obligation(ProofObligation::assume("entering_val", "entering == 9"));
    ctx.push_obligation(ProofObligation::assume(
        "new_sum_def",
        "new_sum == old_sum - leaving + entering",
    ));
    ctx.push_obligation(ProofObligation::assert("slid", "new_sum == 21"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "slide: 15 - 3 + 9 = 21");
}

#[test]
fn window_min_of_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "m"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 8"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "m == if a < b { if a < c { a } else { c } } else { if b < c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("min_val", "m == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window min [8,2,5] = 2");
}

#[test]
fn window_max_of_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "m"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 8"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "m == if a > b { if a > c { a } else { c } } else { if b > c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("max_val", "m == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window max [8,2,5] = 8");
}

#[test]
fn window_average_two() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "avg"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 6"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("avg_def", "avg == (a + b) / 2"));
    ctx.push_obligation(ProofObligation::assert("avg_val", "avg == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "average(6, 10) = 8");
}

#[test]
fn running_sum_four_elements() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "d", "s1", "s2", "s3", "s4"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 4"));
    ctx.push_obligation(ProofObligation::assume("s1_def", "s1 == a"));
    ctx.push_obligation(ProofObligation::assume("s2_def", "s2 == s1 + b"));
    ctx.push_obligation(ProofObligation::assume("s3_def", "s3 == s2 + c"));
    ctx.push_obligation(ProofObligation::assume("s4_def", "s4 == s3 + d"));
    ctx.push_obligation(ProofObligation::assert("total", "s4 == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "running sum [1,2,3,4] = 10");
}

#[test]
fn window_range_span() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "mn", "mx", "span"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "mn_def",
        "mn == if a < b { if a < c { a } else { c } } else { if b < c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "mx_def",
        "mx == if a > b { if a > c { a } else { c } } else { if b > c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assume("span_def", "span == mx - mn"));
    ctx.push_obligation(ProofObligation::assert("range", "span == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window range [3,9,5]: max-min = 9-3 = 6");
}

#[test]
fn window_all_equal() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "sum"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b + c"));
    ctx.push_obligation(ProofObligation::assert("triple", "sum == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window of equal elements [5,5,5] sums to 15");
}

#[test]
fn window_negative_values() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "sum"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0 - 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0 - 2"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b + c"));
    ctx.push_obligation(ProofObligation::assert("mixed_sum", "sum == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "window [-3,7,-2] sums to 2");
}

#[test]
fn window_slide_preserves_size() {
    let mut ctx = VerificationContext::new();
    // Window size stays constant: if we remove one and add one, size unchanged
    for v in &["size", "next_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("size_val", "size == 3"));
    // Remove one element, add one element
    ctx.push_obligation(ProofObligation::assume(
        "next_def",
        "next_size == size - 1 + 1",
    ));
    ctx.push_obligation(ProofObligation::assert("preserved", "next_size == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sliding preserves window size");
}
