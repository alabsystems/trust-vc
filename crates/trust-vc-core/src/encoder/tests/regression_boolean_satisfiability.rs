// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn simple_and() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assert("both_true", "a == 1 && b == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a=1 AND b=1 is satisfiable");
}

#[test]
fn simple_or() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assert("at_least_one", "a == 1 || b == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a=0 OR b=1: at least one is 1");
}

#[test]
fn xor_as_neq() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    ctx.push_obligation(ProofObligation::assert("xor", "a != b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 != 0 models XOR");
}

#[test]
fn implies_via_or() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", i32_ty());
    ctx.declare_var_typed("q", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p_val", "p == 1"));
    ctx.push_obligation(ProofObligation::assume("q_val", "q == 1"));
    ctx.push_obligation(ProofObligation::assert("implies", "!(p == 1) || q == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p=1 implies q=1 (encoded as !p || q)");
}

#[test]
fn modus_ponens() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", i32_ty());
    ctx.declare_var_typed("q", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p_true", "p == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "p_implies_q",
        "!(p == 1) || q == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("q_true", "q == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modus ponens: p AND (p=>q) => q");
}

#[test]
fn contrapositive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", i32_ty());
    ctx.declare_var_typed("q", i32_ty());
    ctx.push_obligation(ProofObligation::assume("not_q", "q == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "p_implies_q",
        "!(p == 1) || q == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("not_p", "p != 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "contrapositive: !q AND (p=>q) => !p");
}

#[test]
fn three_way_and() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "all_true",
        "a == 1 && b == 1 && c == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "three-way AND");
}

#[test]
fn exactly_one_true() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 0"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 1"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 0"));
    ctx.push_obligation(ProofObligation::assert("exactly_one", "a + b + c == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exactly one of {0,1,0} is 1");
}

#[test]
fn at_most_two() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 1"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    ctx.push_obligation(ProofObligation::assume("c_val", "c == 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_two", "a + b + c <= 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "at most two of {1,0,1} are true");
}

#[test]
fn biconditional() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", i32_ty());
    ctx.declare_var_typed("q", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p_val", "p == 1"));
    ctx.push_obligation(ProofObligation::assume("q_val", "q == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "iff",
        "(!(p == 1) || q == 1) && (!(q == 1) || p == 1)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "p <=> q when both true");
}
