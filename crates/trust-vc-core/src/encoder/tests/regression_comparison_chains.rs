// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn transitivity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a < b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b < c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a < b and b < c imply a < c");
}

#[test]
fn antisymmetry() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a <= b"));
    ctx.push_obligation(ProofObligation::assume("ba", "b <= a"));
    ctx.push_obligation(ProofObligation::assert("eq", "a == b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a <= b and b <= a imply a == b");
}

#[test]
fn strict_less_implies_not_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "a < b"));
    ctx.push_obligation(ProofObligation::assert("ne", "a != b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a < b implies a != b");
}

#[test]
fn ge_and_le_is_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a >= b"));
    ctx.push_obligation(ProofObligation::assume("ba", "b >= a"));
    ctx.push_obligation(ProofObligation::assert("eq", "a == b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a >= b and b >= a imply a == b");
}

#[test]
fn less_plus_one_le() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "a < b"));
    ctx.push_obligation(ProofObligation::assert("succ_le", "a + 1 <= b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a < b implies a + 1 <= b");
}

#[test]
fn max_is_ge_both() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("m_val", "m == 5"));
    ctx.push_obligation(ProofObligation::assert("max_ge", "m >= a && m >= b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "m == 5 is >= both 5 and 3");
}

#[test]
fn min_is_le_both() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("m_val", "m == 3"));
    ctx.push_obligation(ProofObligation::assert("min_le", "m <= a && m <= b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "m == 3 is <= both 5 and 3");
}

#[test]
fn chained_three_vars() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a < b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b < c"));
    ctx.push_obligation(ProofObligation::assume("c_bound", "c < 100"));
    ctx.push_obligation(ProofObligation::assert("a_bound", "a < 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a < b, b < c, and c < 100 imply a < 100");
}

#[test]
fn strict_less_not_ge() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "a < b"));
    ctx.push_obligation(ProofObligation::assert("not_ge", "!(a >= b)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a < b implies not (a >= b)");
}

#[test]
fn trichotomy_covers_all() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ne", "a != b"));
    ctx.push_obligation(ProofObligation::assume("not_lt", "!(a < b)"));
    ctx.push_obligation(ProofObligation::assert("gt", "a > b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a != b and not (a < b) imply a > b");
}
