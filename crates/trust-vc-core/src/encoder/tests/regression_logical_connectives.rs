// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn de_morgan_and() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("premise", "!(p && q)"));
    ctx.push_obligation(ProofObligation::assert("claim", "!p || !q"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!(p && q) should imply !p || !q");
}

#[test]
fn de_morgan_or() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("premise", "!(p || q)"));
    ctx.push_obligation(ProofObligation::assert("claim", "!p && !q"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!(p || q) should imply !p && !q");
}

#[test]
fn double_negation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("premise", "!!p"));
    ctx.push_obligation(ProofObligation::assert("claim", "p"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!!p should imply p");
}

#[test]
fn and_idempotent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("claim", "(p && p) == p"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(p && p) should equal p");
}

#[test]
fn or_idempotent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("claim", "(p || p) == p"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "(p || p) should equal p");
}

#[test]
fn and_false_absorb() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("claim", "!(p && false)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p && false should always be false");
}

#[test]
fn or_true_absorb() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("claim", "p || true"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p || true should always hold");
}

#[test]
fn excluded_middle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("claim", "p || !p"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p || !p should always hold");
}

#[test]
fn contradiction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("claim", "!(p && !p)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p && !p should always be false");
}

#[test]
fn material_conditional() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("implication", "!p || q"));
    ctx.push_obligation(ProofObligation::assume("premise", "p"));
    ctx.push_obligation(ProofObligation::assert("claim", "q"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "!p || q and p should imply q");
}
