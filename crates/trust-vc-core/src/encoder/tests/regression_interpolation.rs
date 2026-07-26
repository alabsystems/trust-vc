// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn midpoint_of_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("mid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -100"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 100"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -100"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 100"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("mid_def", "mid == a + (b - a) / 2"));
    ctx.push_obligation(ProofObligation::assert("mid_eq_10", "mid == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "equal endpoints should have midpoint 10");
}

#[test]
fn midpoint_between_zero_and_ten() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("mid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 10"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= 0"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 10"));
    ctx.push_obligation(ProofObligation::assume("a_le_b", "a <= b"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("mid_def", "mid == a + (b - a) / 2"));
    ctx.push_obligation(ProofObligation::assert("mid_eq_5", "mid == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "midpoint between 0 and 10 should be 5");
}

#[test]
fn midpoint_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("mid", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_le_b", "a <= b"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 100"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    ctx.push_obligation(ProofObligation::assume("mid_def", "mid == a + (b - a) / 2"));
    ctx.push_obligation(ProofObligation::assert(
        "mid_in_bounds",
        "mid >= a && mid <= b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "unsigned midpoint should stay within bounds");
}

#[test]
fn linear_interp_at_start() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("t", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_min", "lo >= 0"));
    ctx.push_obligation(ProofObligation::assume("lo_max", "lo <= 100"));
    ctx.push_obligation(ProofObligation::assume("hi_min", "hi >= 0"));
    ctx.push_obligation(ProofObligation::assume("hi_max", "hi <= 100"));
    ctx.push_obligation(ProofObligation::assume("t_min", "t >= 0"));
    ctx.push_obligation(ProofObligation::assume("t_max", "t <= 100"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 100"));
    ctx.push_obligation(ProofObligation::assume("t_val", "t == 0"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == lo + t"));
    ctx.push_obligation(ProofObligation::assert("at_start", "result == lo"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "interpolation at the start should equal the lower bound",
    );
}

#[test]
fn linear_interp_at_end() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("t", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_min", "lo >= 0"));
    ctx.push_obligation(ProofObligation::assume("lo_max", "lo <= 100"));
    ctx.push_obligation(ProofObligation::assume("hi_min", "hi >= 0"));
    ctx.push_obligation(ProofObligation::assume("hi_max", "hi <= 100"));
    ctx.push_obligation(ProofObligation::assume("t_min", "t >= 0"));
    ctx.push_obligation(ProofObligation::assume("t_max", "t <= 100"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 0"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 100"));
    ctx.push_obligation(ProofObligation::assume("t_val", "t == 100"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == lo + t"));
    ctx.push_obligation(ProofObligation::assert("at_end", "result == hi"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "interpolation at the end should equal the upper bound",
    );
}

#[test]
fn average_of_two_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("avg", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -100"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 100"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -100"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 100"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("avg_def", "avg == (a + b) / 2"));
    ctx.push_obligation(ProofObligation::assert("avg_eq_7", "avg == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "equal values should have average 7");
}

#[test]
fn average_in_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("avg", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 8"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= 0"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 8"));
    ctx.push_obligation(ProofObligation::assume("a_le_b", "a <= b"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 8"));
    ctx.push_obligation(ProofObligation::assume("avg_def", "avg == (a + b) / 2"));
    ctx.push_obligation(ProofObligation::assert(
        "avg_in_range",
        "avg >= 4 && avg <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "average should stay within the endpoint range");
}

#[test]
fn quarter_point() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("q", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_le_b", "a <= b"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 100"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    ctx.push_obligation(ProofObligation::assume("q_def", "q == a + (b - a) / 4"));
    ctx.push_obligation(ProofObligation::assert("q_eq_25", "q == 25"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "quarter point should evaluate to 25");
}

#[test]
fn three_quarter_point() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("q", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_le_b", "a <= b"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 100"));
    ctx.push_obligation(ProofObligation::assume("span_max", "b - a <= 100"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 100"));
    ctx.push_obligation(ProofObligation::assume("q_def", "q == a + 3 * (b - a) / 4"));
    ctx.push_obligation(ProofObligation::assert("q_eq_75", "q == 75"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "three-quarter point should evaluate to 75");
}

#[test]
fn clamped_midpoint() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lo", i32_ty());
    ctx.declare_var_typed("hi", i32_ty());
    ctx.declare_var_typed("mid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lo_min", "lo >= 0"));
    ctx.push_obligation(ProofObligation::assume("lo_max", "lo <= 20"));
    ctx.push_obligation(ProofObligation::assume("hi_min", "hi >= 0"));
    ctx.push_obligation(ProofObligation::assume("hi_max", "hi <= 20"));
    ctx.push_obligation(ProofObligation::assume("lo_le_hi", "lo <= hi"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 10"));
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "mid_def",
        "mid == lo + (hi - lo) / 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mid_clamped",
        "mid >= lo && mid <= hi",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "midpoint should remain within clamped bounds");
}
