// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn const_add() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_add", "2 + 3 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "2 + 3 should equal 5");
}

#[test]
fn const_mul() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_mul", "6 * 7 == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "6 * 7 should equal 42");
}

#[test]
fn const_sub() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_sub", "10 - 3 == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "10 - 3 should equal 7");
}

#[test]
fn const_div() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_div", "15 / 3 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "15 / 3 should equal 5");
}

#[test]
fn const_mod() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_mod", "17 % 5 == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "17 % 5 should equal 2");
}

#[test]
fn const_nested_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "const_nested_arithmetic",
        "(2 + 3) * (4 + 1) == 25",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(2 + 3) * (4 + 1) should equal 25");
}

#[test]
fn const_comparison() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "const_comparison",
        "5 > 3 && 3 < 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "5 > 3 && 3 < 5 should verify");
}

#[test]
fn const_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_boolean", "true && !false"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "true && !false should verify");
}

#[test]
fn const_shift() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_shift", "(1 << 10) == 1024"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 << 10 should equal 1024");
}

#[test]
fn const_bitwise() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("const_bitwise", "(255 & 15) == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "255 & 15 should equal 15");
}
