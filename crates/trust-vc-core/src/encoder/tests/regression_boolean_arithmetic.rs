// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn true_and_true() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("both_true", "p && q"));
    ctx.push_obligation(ProofObligation::assert("assert_p", "p"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p should hold when p && q is assumed");
}

#[test]
fn false_or_anything() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("not_p", "!p"));
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("disjunction", "!p || q"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!p || q should hold when !p is assumed");
}

#[test]
fn bool_eq_refl() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("refl", "p == p"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boolean equality should be reflexive");
}

#[test]
fn not_true_is_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("not_true", "!true == false"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!true should equal false");
}

#[test]
fn not_false_is_true() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("not_false", "!false == true"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!false should equal true");
}

#[test]
fn bool_xor_different() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("xor_case", "p && !q"));
    ctx.push_obligation(ProofObligation::assert("different", "p != q"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p and !q should imply p != q");
}

#[test]
fn and_commutes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "and_commutes",
        "(p && q) == (q && p)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boolean conjunction should commute");
}

#[test]
fn or_commutes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "or_commutes",
        "(p || q) == (q || p)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boolean disjunction should commute");
}

#[test]
fn bool_implies_modus_ponens() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("premises", "(!p || q) && p"));
    ctx.push_obligation(ProofObligation::assert("conclusion", "q"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(!p || q) && p should imply q");
}

#[test]
fn bool_contrapositive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("premises", "(!p || q) && !q"));
    ctx.push_obligation(ProofObligation::assert("conclusion", "!p"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(!p || q) && !q should imply !p");
}
