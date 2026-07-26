// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn addition_commutative_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "addition_commutative",
        "a + b == b + a",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "concrete addition should be commutative");
}

#[test]
fn addition_commutative_symbolic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "addition_commutative",
        "a + b == b + a",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded symbolic addition should be commutative");
}

#[test]
fn multiplication_commutative_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 4"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "multiplication_commutative",
        "a * b == b * a",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "concrete multiplication commutativity may use fallback reasoning",
    );
}

#[test]
fn min_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 8"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "min_commutative",
        "if a < b { a } else { b } == if b < a { b } else { a }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min should be commutative for concrete values");
}

#[test]
fn max_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 8"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "max_commutative",
        "if a > b { a } else { b } == if b > a { b } else { a }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max should be commutative for concrete values");
}

#[test]
fn equality_symmetric() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("equal", "a == b"));
    ctx.push_obligation(ProofObligation::assert("equality_symmetric", "b == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equality should be symmetric");
}

#[test]
fn xor_commutative_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 12"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "xor_commutative",
        "(a ^ b) == (b ^ a)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR commutativity may need fallback reasoning");
}

#[test]
fn and_commutative_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 15"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assert(
        "and_commutative",
        "(a & b) == (b & a)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "AND commutativity may need fallback reasoning");
}

#[test]
fn or_commutative_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 15"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assert(
        "or_commutative",
        "(a | b) == (b | a)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "OR commutativity may need fallback reasoning");
}

#[test]
fn subtraction_anticommutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "subtraction_anticommutative",
        "a - b == 0 - (b - a)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "subtraction should satisfy this anticommutative identity",
    );
}
