// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn nested_if_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x > 0 { if x > 5 { 2 } else { 1 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_2", "y == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 > 5 > 0 so y=2");
}

#[test]
fn nested_if_middle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x > 0 { if x > 5 { 2 } else { 1 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_1", "y == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 > 0 but 3 <= 5 so y=1");
}

#[test]
fn nested_if_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 1"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x > 0 { if x > 5 { 2 } else { 1 } } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_0", "y == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "-1 <= 0 so y=0");
}

#[test]
fn grade_a() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("score", i32_ty());
    ctx.declare_var_typed("grade", i32_ty());
    ctx.push_obligation(ProofObligation::assume("score_val", "score == 95"));
    ctx.push_obligation(ProofObligation::assume(
        "grade_def",
        "grade == if score >= 90 { 4 } else { if score >= 80 { 3 } else { if score >= 70 { 2 } else { 1 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("grade_is_4", "grade == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "score 95 => grade A (4)");
}

#[test]
fn grade_b() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("score", i32_ty());
    ctx.declare_var_typed("grade", i32_ty());
    ctx.push_obligation(ProofObligation::assume("score_val", "score == 85"));
    ctx.push_obligation(ProofObligation::assume(
        "grade_def",
        "grade == if score >= 90 { 4 } else { if score >= 80 { 3 } else { if score >= 70 { 2 } else { 1 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("grade_is_3", "grade == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "score 85 => grade B (3)");
}

#[test]
fn grade_c() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("score", i32_ty());
    ctx.declare_var_typed("grade", i32_ty());
    ctx.push_obligation(ProofObligation::assume("score_val", "score == 75"));
    ctx.push_obligation(ProofObligation::assume(
        "grade_def",
        "grade == if score >= 90 { 4 } else { if score >= 80 { 3 } else { if score >= 70 { 2 } else { 1 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("grade_is_2", "grade == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "score 75 => grade C (2)");
}

#[test]
fn two_conditions_combined() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.declare_var_typed("result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == if x > y { x } else { y }",
    ));
    ctx.push_obligation(ProofObligation::assert("max_is_7", "result == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max(3, 7) = 7");
}

#[test]
fn chained_min() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("m1", i32_ty());
    ctx.declare_var_typed("m2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "m1_def",
        "m1 == if a < b { a } else { b }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "m2_def",
        "m2 == if m1 < c { m1 } else { c }",
    ));
    ctx.push_obligation(ProofObligation::assert("min_is_2", "m2 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min(5, 2, 8) = 2");
}

#[test]
fn median_of_three() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "c", "med"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "med_def",
        "med == if a >= b && a <= c { a } else { if b >= a && b <= c { b } else { c } }",
    ));
    ctx.push_obligation(ProofObligation::assert("med_is_2", "med == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "median(3, 1, 2) = 2");
}

#[test]
fn ternary_cascade_last() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "y_def",
        "y == if x > 10 { 3 } else { if x > 5 { 2 } else { if x > 0 { 1 } else { 0 } } }",
    ));
    ctx.push_obligation(ProofObligation::assert("y_is_0", "y == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x=0 falls through to last branch");
}
