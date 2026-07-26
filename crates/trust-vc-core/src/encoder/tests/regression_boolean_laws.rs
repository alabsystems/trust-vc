//! Boolean law regression tests.
//!
//! These tests verify that the encoder correctly handles boolean identities:
//! De Morgan laws, absorption, distribution, double negation, etc.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn boolean_de_morgan_and() {
    // !(a && b) == (!a || !b)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "de_morgan_and",
        "(!(a && b)) == (!a || !b)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "De Morgan AND law should verify");
}

#[test]
fn boolean_de_morgan_or() {
    // !(a || b) == (!a && !b)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "de_morgan_or",
        "(!(a || b)) == (!a && !b)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "De Morgan OR law should verify");
}

#[test]
fn boolean_double_negation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("double_neg", "!!a == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Double negation should verify");
}

#[test]
fn boolean_and_identity_true() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("and_true", "(a && true) == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a AND true should equal a");
}

#[test]
fn boolean_or_identity_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("or_false", "(a || false) == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a OR false should equal a");
}

#[test]
fn boolean_and_annihilation_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "and_false",
        "(a && false) == false",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a AND false should equal false");
}

#[test]
fn boolean_or_annihilation_true() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("or_true", "(a || true) == true"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a OR true should equal true");
}

#[test]
fn boolean_and_idempotent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("and_idem", "(a && a) == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a AND a should equal a");
}

#[test]
fn boolean_or_idempotent() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("or_idem", "(a || a) == a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a OR a should equal a");
}

#[test]
fn boolean_and_complement() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("and_comp", "(a && !a) == false"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a AND !a should equal false");
}

#[test]
fn boolean_or_complement() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("or_comp", "(a || !a) == true"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "a OR !a should equal true");
}

#[test]
fn boolean_and_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("and_comm", "(a && b) == (b && a)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AND should be commutative");
}

#[test]
fn boolean_or_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("or_comm", "(a || b) == (b || a)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OR should be commutative");
}

#[test]
fn boolean_and_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("c", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "and_assoc",
        "((a && b) && c) == (a && (b && c))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "AND should be associative");
}

#[test]
fn boolean_or_associative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("c", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert(
        "or_assoc",
        "((a || b) || c) == (a || (b || c))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "OR should be associative");
}
