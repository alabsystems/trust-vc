// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn range_implies_bound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "x >= 5 && x <= 10"));
    ctx.push_obligation(ProofObligation::assert("bound", "x >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "range [5, 10] should imply x >= 0");
}

#[test]
fn range_sum_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ranges",
        "a >= 0 && a <= 50 && b >= 0 && b <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert("sum_bound", "a + b <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two values in [0, 50] should sum to at most 100");
}

#[test]
fn range_product_sign() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ranges",
        "a >= 1 && a <= 10 && b >= 1 && b <= 10",
    ));
    // The bounds constrain the product to 1..=100, so mathematical-integer
    // reasoning is equivalent to i32 multiplication for this obligation.
    ctx.push_obligation(
        ProofObligation::assert("product_sign", "a * b >= 1")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "positive ranges should imply product is at least 1",
    );

    // The former verified-or-unknown oracle could hide a proof-resource
    // regression. Pin the lower endpoint and require a real counterexample to
    // the adjacent false claim as a control for the explicit tactic.
    ctx.push_obligation(ProofObligation::assume("a_at_lower_endpoint", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_at_lower_endpoint", "b == 1"));
    ctx.push_obligation(
        ProofObligation::assert("false_product_sign", "a * b > 1")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "the nonlinear tactic must reject 1 * 1 > 1");
}

#[test]
fn range_exclude_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_without_five",
        "x >= 0 && x <= 10 && x != 5",
    ));
    ctx.push_obligation(ProofObligation::assert("exclude_value", "x <= 4 || x >= 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "excluding 5 from [0, 10] should force x outside 5");
}

#[test]
fn range_tighten() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "base_range",
        "x >= 0 && x <= 100 && x >= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tightened_range",
        "x >= 50 && x <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "combined bounds should tighten x to [50, 100]");
}

#[test]
fn range_negation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "x >= -10 && x <= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "negated_range",
        "-x >= -10 && -x <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "negating a value in [-10, 10] should stay in [-10, 10]",
    );
}

#[test]
fn range_shift() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "x >= 0 && x <= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "shifted_range",
        "x + 10 >= 10 && x + 10 <= 110",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shifting [0, 100] by 10 should yield [10, 110]");
}

#[test]
fn range_halve() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "x >= 0 && x <= 100"));
    ctx.push_obligation(ProofObligation::assert("half_bound", "x / 2 <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "halving a u32 in [0, 100] should stay at most 50");
}

#[test]
fn range_overlap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("first_range", "x >= 0 && x <= 20"));
    ctx.push_obligation(ProofObligation::assume(
        "second_range",
        "x >= 10 && x <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert("overlap", "x >= 10 && x <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "overlapping ranges should constrain x to [10, 20]");
}

#[test]
fn range_union_cover() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "x >= 0 && x <= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "union_cover",
        "(x <= 50) || (x >= 51)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "every value in [0, 100] should be at most 50 or at least 51",
    );
}
