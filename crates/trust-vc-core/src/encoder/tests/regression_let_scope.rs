//! Let binding and scope regression tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn let_simple_binding() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_eq_x", "y == x"));
    ctx.push_obligation(ProofObligation::assert("y_is_5", "y == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "simple variable binding propagates");
}

#[test]
fn let_sum_binding() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("sum", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    ctx.push_obligation(ProofObligation::assert("sum_is_7", "sum == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sum binding");
}

#[test]
fn let_shadow_independent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 20"));
    ctx.push_obligation(ProofObligation::assert("independent", "x + y == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "independent variables sum correctly");
}

#[test]
fn let_chain_three_vars() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_from_a", "b == a + 1"));
    ctx.push_obligation(ProofObligation::assume("c_from_b", "c == b + 1"));
    ctx.push_obligation(ProofObligation::assert("c_is_3", "c == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chained variable definitions");
}

#[test]
fn let_bool_binding() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("flag", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("x_pos", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("flag_def", "flag == (x > 0)"));
    ctx.push_obligation(ProofObligation::assert("flag_true", "flag == true"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boolean binding from comparison");
}

#[test]
fn let_multiple_assumptions_consistent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pos", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("bounded", "x < 100"));
    ctx.push_obligation(ProofObligation::assert("in_range", "x >= 1 && x <= 99"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multiple assumptions combine correctly");
}

#[test]
fn let_contradictory_assumptions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pos", "x > 0"));
    ctx.push_obligation(ProofObligation::assume("neg", "x < 0"));
    ctx.push_obligation(ProofObligation::assert("anything", "x == 42"));
    let result = AYEncoder::verify(&ctx);
    // TrustVc detects contradictory assumptions and reports Unknown (vacuous truth).
    expect_unknown(&result, "contradictory assumptions detected as vacuous");
}

#[test]
fn let_zero_sum_property() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("opposite", "b == -a"));
    ctx.push_obligation(ProofObligation::assume("not_min", "a > -2147483648"));
    ctx.push_obligation(ProofObligation::assert("zero_sum", "a + b == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a + (-a) == 0");
}

#[test]
fn let_max_of_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("m_is_max", "m == a"));
    ctx.push_obligation(ProofObligation::assert("m_ge_both", "m >= a && m >= b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max(7,3) >= both");
}

#[test]
fn let_swap_values() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("tmp", i32_ty());
    ctx.declare_var_typed("a2", i32_ty());
    ctx.declare_var_typed("b2", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume("tmp_def", "tmp == a"));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == b"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == tmp"));
    ctx.push_obligation(ProofObligation::assert("swapped", "a2 == 2 && b2 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swap via temp variable");
}
