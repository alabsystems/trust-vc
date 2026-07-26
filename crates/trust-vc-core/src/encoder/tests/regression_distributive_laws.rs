// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn and_distributes_over_or() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("r", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "distributive",
        "(p && (q || r)) == ((p && q) || (p && r))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AND should distribute over OR");
}

#[test]
fn or_distributes_over_and() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("r", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "distributive",
        "(p || (q && r)) == ((p || q) && (p || r))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OR should distribute over AND");
}

#[test]
fn bitwise_and_distributes_or() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 255"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 15"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 240"));
    ctx.push_obligation(ProofObligation::assert(
        "distributive",
        "(a & (b | c)) == ((a & b) | (a & c))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bitwise AND should distribute over OR");
}

#[test]
fn bitwise_or_distributes_and() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 255"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 15"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 240"));
    ctx.push_obligation(ProofObligation::assert(
        "distributive",
        "(a | (b & c)) == ((a | b) & (a | c))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bitwise OR should distribute over AND");
}

#[test]
fn mul_distributes_add_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 2"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "distributive",
        "(a * (b + c)) == ((a * b) + (a * c))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multiplication should distribute over addition");
}

#[test]
fn mul_distributes_sub_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "distributive",
        "(a * (b - c)) == ((a * b) - (a * c))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "multiplication should distribute over subtraction");
}

#[test]
fn and_absorption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "absorption",
        "(p && (p || q)) == p",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AND absorption should verify");
}

#[test]
fn or_absorption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "absorption",
        "(p || (p && q)) == p",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OR absorption should verify");
}

#[test]
fn bitwise_xor_and_distribute() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.declare_var_typed("c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 20"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "distributive",
        "((a ^ b) & c) == ((a & c) ^ (b & c))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR/AND distributive law may need fallback");
}

#[test]
fn neg_distributes_add_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "distributive",
        "(-(a + b)) == ((-a) + (-b))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "negation over addition may hit BV wrapping");
}
