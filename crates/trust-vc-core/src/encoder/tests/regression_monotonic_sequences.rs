// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn strictly_increasing_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assert("chain", "a < b && b < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 < 2 < 3 forms a strict increasing chain");
}

#[test]
fn weakly_increasing_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 7"));
    ctx.push_obligation(ProofObligation::assert("chain", "a <= b && b <= c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 <= 5 <= 7 forms a weak increasing chain");
}

#[test]
fn strictly_decreasing_three() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assert("chain", "a > b && b > c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 > 7 > 3 forms a strict decreasing chain");
}

#[test]
fn monotone_implies_endpoints() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_lo", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_hi", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_lo", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_hi", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assume("c_lo", "c >= -1000"));
    ctx.push_obligation(ProofObligation::assume("c_hi", "c <= 1000"));
    ctx.push_obligation(ProofObligation::assume("ab", "a < b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b < c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "strict monotone chains preserve endpoint ordering");
}

#[test]
fn increasing_by_one() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.declare_var_typed("d", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_step", "b == a + 1"));
    ctx.push_obligation(ProofObligation::assume("c_step", "c == b + 1"));
    ctx.push_obligation(ProofObligation::assume("d_step", "d == c + 1"));
    ctx.push_obligation(ProofObligation::assert("d_val", "d == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "incrementing from 0 by one three times yields 3");
}

#[test]
fn decreasing_by_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_lo", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_hi", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_lo", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_hi", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assume("c_lo", "c >= -1000"));
    ctx.push_obligation(ProofObligation::assume("c_hi", "c <= 1000"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 20"));
    ctx.push_obligation(ProofObligation::assume("b_step", "b == a - 2"));
    ctx.push_obligation(ProofObligation::assume("c_step", "c == b - 2"));
    ctx.push_obligation(ProofObligation::assert("c_val", "c == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "decrementing 20 by two twice yields 16");
}

#[test]
fn gap_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 30"));
    ctx.push_obligation(ProofObligation::assert("gap", "b - a == c - b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equal spacing is preserved across the chain");
}

#[test]
fn monotone_sum_lower_bound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_lo", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("a_hi", "a <= 100"));
    ctx.push_obligation(ProofObligation::assume("b_lo", "b >= 0"));
    ctx.push_obligation(ProofObligation::assume("b_hi", "b <= 100"));
    ctx.push_obligation(ProofObligation::assume("c_lo", "c >= 0"));
    ctx.push_obligation(ProofObligation::assume("c_hi", "c <= 100"));
    ctx.push_obligation(ProofObligation::assume("ab", "a <= b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b <= c"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 5"));
    ctx.push_obligation(ProofObligation::assert("sum_lb", "a + b + c >= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "monotone bounded values imply the requested sum lower bound",
    );
}

#[test]
fn five_element_chain() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.declare_var_typed("d", u32_ty());
    ctx.declare_var_typed("e", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 6"));
    ctx.push_obligation(ProofObligation::assume("d_val", "d == 8"));
    ctx.push_obligation(ProofObligation::assume("e_val", "e == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "chain",
        "a < b && b < c && c < d && d < e",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "2 < 4 < 6 < 8 < 10 forms a five-element increasing chain",
    );
}

#[test]
fn monotone_max_is_last() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a < b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b < c"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 100"));
    ctx.push_obligation(ProofObligation::assert("max", "c >= a && c >= b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "the last element of a strict increasing chain is the maximum",
    );
}
