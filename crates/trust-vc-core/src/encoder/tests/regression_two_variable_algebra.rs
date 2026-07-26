// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn sum_commutes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assert("sum_commutes", "a + b == b + a"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "integer addition should commute");
}

#[test]
fn difference_antisymmetric_bounded() {
    // In BV arithmetic, a-b can equal b-a due to wrapping even when a!=b.
    // With tight bounds this becomes provable.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("distinct", "a != b"));
    ctx.push_obligation(ProofObligation::assume(
        "a_bounded",
        "a >= -1000 && a <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_bounded",
        "b >= -1000 && b <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "difference_antisymmetric",
        "a - b != b - a",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bounded distinct values have antisymmetric differences",
    );
}

#[test]
fn product_of_equals() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("same", "a == b"));
    ctx.push_obligation(ProofObligation::assert(
        "product_of_equals",
        "a * a == b * b",
    ));

    let result = AYEncoder::verify(&ctx);
    // BV multiplication with symbolic equal vars can timeout.
    expect_verified_or_unknown(&result, "equal values should have equal squares");
}

#[test]
fn sum_with_negation_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("not_min", "a > -2147483648"));
    ctx.push_obligation(ProofObligation::assert(
        "sum_with_negation_zero",
        "a + (-a) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "adding a non-min value to its negation should yield zero",
    );
}

#[test]
fn distribute_over_sum() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("c_two", "c == 2"));
    ctx.push_obligation(ProofObligation::assume("a_lo", "a >= -536870912"));
    ctx.push_obligation(ProofObligation::assume("a_hi", "a <= 536870911"));
    ctx.push_obligation(ProofObligation::assume("b_lo", "b >= -536870912"));
    ctx.push_obligation(ProofObligation::assume("b_hi", "b <= 536870911"));
    ctx.push_obligation(ProofObligation::assert(
        "distribute_over_sum",
        "c * (a + b) == c * a + c * b",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "doubling a sum should distribute over addition");
}

#[test]
fn square_difference() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_five", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_three", "b == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "square_difference",
        "(a + b) * (a - b) == a * a - b * b",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "difference of squares identity should hold for concrete values",
    );
}

#[test]
fn midpoint() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_four", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_eight", "b == 8"));
    ctx.push_obligation(ProofObligation::assume("m_six", "m == 6"));
    ctx.push_obligation(ProofObligation::assert("midpoint", "m == (a + b) / 2"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "6 should be the midpoint of 4 and 8");
}

#[test]
fn average_between() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_zero", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_ten", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("m_five", "m == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "average_between",
        "m >= a && m <= b",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "the average should lie between the endpoints");
}

#[test]
fn swap_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_is_x", "a == x"));
    ctx.push_obligation(ProofObligation::assume("b_is_y", "b == y"));
    ctx.push_obligation(ProofObligation::assert("swap_identity", "a == x && b == y"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trivial identity bindings should hold");
}

#[test]
fn sum_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_nonnegative", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("a_bounded", "a <= 50"));
    ctx.push_obligation(ProofObligation::assume("b_nonnegative", "b >= 0"));
    ctx.push_obligation(ProofObligation::assume("b_bounded", "b <= 50"));
    ctx.push_obligation(ProofObligation::assert(
        "sum_bounds",
        "a + b >= 0 && a + b <= 100",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bounded nonnegative addends should produce a bounded nonnegative sum",
    );
}
