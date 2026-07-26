// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn trichotomy() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assert(
        "trichotomy",
        "(a < b) || (a == b) || (a > b)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trichotomy should hold for i32 values");
}

#[test]
fn strict_order_transitive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a < b && b < c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "strict order should be transitive");
}

#[test]
fn weak_order_transitive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a <= b && b <= c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a <= c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "weak order should be transitive");
}

#[test]
fn antisymmetric() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a <= b && b <= a"));
    ctx.push_obligation(ProofObligation::assert("eq", "a == b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "antisymmetry should force equality");
}

#[test]
fn three_ordered() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "ordered",
        "a < b && b < c && a < c",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 < 2 < 3 should hold");
}

#[test]
fn four_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.declare_var_typed("d", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "chain",
        "a < b && b < c && c < d && a < d",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 < 2 < 3 < 4 should imply 1 < 4");
}

#[test]
fn max_of_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assert("max", "b >= a && b >= c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 should be the maximum of 3, 7, and 5");
}

#[test]
fn min_of_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assert("min", "a <= b && a <= c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 should be the minimum of 3, 7, and 5");
}

#[test]
fn sorted_triple() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sorted", "a <= b && b <= c"));
    ctx.push_obligation(ProofObligation::assert("ordered", "a <= c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sorted triple should preserve endpoint ordering");
}

#[test]
fn between_squeeze() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("chain", "a < b && b < c"));
    ctx.push_obligation(ProofObligation::assume("a_bound", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("c_bound", "c <= 1000"));
    ctx.push_obligation(ProofObligation::assert("squeeze", "a + 1 <= b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "strictly between values should differ by at least one",
    );
}
