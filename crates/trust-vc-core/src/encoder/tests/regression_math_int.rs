// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn math_int_add_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assert("commut", "a + b == b + a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int addition is commutative");
}

#[test]
fn math_int_add_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("c", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assert(
        "assoc",
        "(a + b) + c == a + (b + c)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int addition is associative");
}

#[test]
fn math_int_mul_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assert("commut", "a * b == b * a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int multiplication is commutative");
}

#[test]
fn math_int_additive_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assert("identity", "a + 0 == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int additive identity holds");
}

#[test]
fn math_int_mul_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assert("identity", "a * 1 == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int multiplicative identity holds");
}

#[test]
fn math_int_sub_self_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assert("self_zero", "a - a == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int subtraction by self yields zero");
}

#[test]
fn math_int_double_equals_two_times_a() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assert("double", "a + a == 2 * a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int doubling matches multiplication by two");
}

#[test]
fn math_int_mul_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assert("mul_zero", "a * 0 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int multiplication by zero yields zero");
}

#[test]
fn math_int_add_negate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assume("sum_zero", "a + b == 0"));
    ctx.push_obligation(ProofObligation::assert("negate", "b == -a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int additive inverse follows from zero sum");
}

#[test]
fn math_int_large_constant_works() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 999999999999999"));
    ctx.push_obligation(ProofObligation::assert("positive", "x > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "math int large constant remains positive");
}
