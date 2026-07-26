// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pinch_to_value() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_ge_5", "x >= 5"));
    ctx.push_obligation(ProofObligation::assume("x_le_5", "x <= 5"));
    ctx.push_obligation(ProofObligation::assert("x_eq_5", "x == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x >= 5 and x <= 5 should force x == 5");
}

#[test]
fn triangle_inequality_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "triangle_ineq",
        "a + b > c && b + c > a && a + c > b",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3, 4, 5 should satisfy the triangle inequalities");
}

#[test]
fn linear_system() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    // Bound to prevent BV wrapping counterexamples.
    ctx.push_obligation(ProofObligation::assume(
        "x_bound",
        "x >= -1000 && x <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "y_bound",
        "y >= -1000 && y <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("sum_eq_10", "x + y == 10"));
    ctx.push_obligation(ProofObligation::assume("diff_eq_4", "x - y == 4"));
    ctx.push_obligation(ProofObligation::assert("solution", "x == 7 && y == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bounded linear system should solve to x == 7 and y == 3",
    );
}

#[test]
fn bounded_quadrant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_ge_0", "x >= 0"));
    ctx.push_obligation(ProofObligation::assume("x_le_10", "x <= 10"));
    ctx.push_obligation(ProofObligation::assume("y_ge_0", "y >= 0"));
    ctx.push_obligation(ProofObligation::assume("y_le_10", "y <= 10"));
    ctx.push_obligation(ProofObligation::assert("sum_le_20", "x + y <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two values in [0, 10] should sum to at most 20");
}

#[test]
fn elimination() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    // Bound to prevent BV wrapping counterexamples.
    ctx.push_obligation(ProofObligation::assume(
        "a_bound",
        "a >= -1000 && a <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "b_bound",
        "b >= -1000 && b <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "c_bound",
        "c >= -1000 && c <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("ab_sum", "a + b == 10"));
    ctx.push_obligation(ProofObligation::assume("bc_sum", "b + c == 15"));
    ctx.push_obligation(ProofObligation::assume("ac_sum", "a + c == 13"));
    ctx.push_obligation(ProofObligation::assert(
        "solution",
        "a == 4 && b == 6 && c == 9",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bounded pairwise sums should determine a, b, and c",
    );
}

#[test]
fn nested_bounds() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_ge_0", "x >= 0"));
    ctx.push_obligation(ProofObligation::assume("x_le_y", "x <= y"));
    ctx.push_obligation(ProofObligation::assume("y_le_10", "y <= 10"));
    ctx.push_obligation(ProofObligation::assert("x_le_10", "x <= 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x <= y and y <= 10 should imply x <= 10");
}

#[test]
fn modular_constraint() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_mod_3", "x % 3 == 0"));
    ctx.push_obligation(ProofObligation::assume("x_ge_0", "x >= 0"));
    ctx.push_obligation(ProofObligation::assume("x_le_9", "x <= 9"));
    ctx.push_obligation(ProofObligation::assert(
        "enumerated_values",
        "x == 0 || x == 3 || x == 6 || x == 9",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a multiple of 3 in [0, 9] should be one of 0, 3, 6, or 9",
    );
}

#[test]
fn sum_product() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sum_eq_7", "a + b == 7"));
    ctx.push_obligation(ProofObligation::assume("a_eq_3", "a == 3"));
    ctx.push_obligation(ProofObligation::assert("b_eq_4", "b == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a + b == 7 and a == 3 should force b == 4");
}

#[test]
fn chain_implications() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.declare_var_typed("z", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("y_succ", "y == x + 1"));
    ctx.push_obligation(ProofObligation::assume("z_succ", "z == y + 1"));
    ctx.push_obligation(ProofObligation::assert("z_offset", "z == x + 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "successor equalities should collapse to z == x + 2",
    );
}

#[test]
fn range_intersection_point() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_ge_5", "x >= 5"));
    ctx.push_obligation(ProofObligation::assume("x_le_7", "x <= 7"));
    ctx.push_obligation(ProofObligation::assume("x_even", "x % 2 == 0"));
    ctx.push_obligation(ProofObligation::assert("x_eq_6", "x == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "the only even value in [5, 7] should be 6");
}
