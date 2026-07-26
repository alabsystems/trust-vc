// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn bool_ite_true_branch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("cond_true", "cond == true"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("ite_result", "x == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "true branch taken correctly");
}

#[test]
fn bool_ite_false_branch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("cond_false", "cond == false"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 9"));
    ctx.push_obligation(ProofObligation::assert(
        "ite_result",
        "if cond { 5 } else { x } == 9",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "false branch taken correctly");
}

#[test]
fn bool_negation_double() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("double_neg", "!!a == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "double boolean negation should verify");
}

#[test]
fn bool_and_short_circuit_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "and_false",
        "(a && false) == false",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a && false should reduce to false");
}

#[test]
fn bool_or_short_circuit_true() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("or_true", "(a || true) == true"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a || true should reduce to true");
}

#[test]
fn bool_xor_self_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("xor_self", "(a != a) == false"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boolean xor with itself should be false");
}

#[test]
fn bool_conditional_equality() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("cond_true", "cond == true"));
    ctx.push_obligation(ProofObligation::assume("eq_when_cond", "!cond || (x == y)"));
    ctx.push_obligation(ProofObligation::assert("eq_result", "x == y"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conditional equality should discharge under cond");
}

#[test]
fn bool_mux_pattern() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("cond_true", "cond == true"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 11"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 22"));
    ctx.push_obligation(ProofObligation::assert(
        "mux_result",
        "if cond { a } else { b } == 11",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mux pattern should select the then branch");
}

#[test]
fn bool_nested_conditionals() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("outer", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("inner", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("y", crate::ir::TrustVcType::Int { width: 32 });
    ctx.declare_var_typed("z", crate::ir::TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assume("outer_true", "outer == true"));
    ctx.push_obligation(ProofObligation::assume("inner_false", "inner == false"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 1"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 2"));
    ctx.push_obligation(ProofObligation::assume("z_val", "z == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "nested_result",
        "if outer { if inner { x } else { y } } else { z } == 2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nested conditionals should pick the inner else branch",
    );
}

#[test]
fn bool_implies_equiv_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "implies_equiv",
        "(if a { b } else { true }) == (!a || b)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a implies b should match !a || b");
}
