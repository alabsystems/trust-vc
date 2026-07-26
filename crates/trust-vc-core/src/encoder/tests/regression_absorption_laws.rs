// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn and_absorption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0xFF"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0x0F"));
    ctx.push_obligation(ProofObligation::assert(
        "and_absorption",
        "(a & (a | b)) == a",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise AND absorption may need fallback reasoning",
    );
}

#[test]
fn or_absorption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0xFF"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0x0F"));
    ctx.push_obligation(ProofObligation::assert(
        "or_absorption",
        "(a | (a & b)) == a",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bitwise OR absorption may need fallback reasoning");
}

#[test]
fn and_complement_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "and_complement_is_zero",
        "(a & (a ^ 4294967295)) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise AND with the xor-complement may need fallback reasoning",
    );
}

#[test]
fn or_complement_is_all_ones() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "or_complement_is_all_ones",
        "(a | (a ^ 4294967295)) == 4294967295",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise OR with the xor-complement may need fallback reasoning",
    );
}

#[test]
fn distribute_and_over_or() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0xFF"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0x0F"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0xF0"));
    ctx.push_obligation(ProofObligation::assert(
        "distribute_and_over_or",
        "(a & (b | c)) == ((a & b) | (a & c))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise AND distribution over OR may need fallback reasoning",
    );
}

#[test]
fn distribute_or_over_and() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0xFF"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0x0F"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0xF0"));
    ctx.push_obligation(ProofObligation::assert(
        "distribute_or_over_and",
        "(a | (b & c)) == ((a | b) & (a | c))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise OR distribution over AND may need fallback reasoning",
    );
}

#[test]
fn xor_with_zero_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "xor_with_zero_identity",
        "(a ^ 0) == a",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bitwise XOR identity may need fallback reasoning");
}

#[test]
fn and_with_all_ones_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "and_with_all_ones_identity",
        "(a & 4294967295) == a",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise AND with all ones may need fallback reasoning",
    );
}

#[test]
fn or_with_zero_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "or_with_zero_identity",
        "(a | 0) == a",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bitwise OR identity may need fallback reasoning");
}

#[test]
fn and_with_zero_annihilation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assert(
        "and_with_zero_annihilation",
        "(a & 0) == 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "bitwise AND annihilation by zero may need fallback reasoning",
    );
}
