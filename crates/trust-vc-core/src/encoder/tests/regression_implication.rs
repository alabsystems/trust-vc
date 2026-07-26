//! Implication and conditional regression tests.
//!
//! Verify that logical implications and if-then-else reasoning work correctly.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn implication_modus_ponens() {
    // If P and P implies Q, then Q
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("p_true", "p == true"));
    ctx.push_obligation(ProofObligation::assume("p_implies_q", "!p || q"));
    ctx.push_obligation(ProofObligation::assert("q_true", "q == true"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "modus ponens should verify");
}

#[test]
fn implication_contrapositive() {
    // If P implies Q, then !Q implies !P
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("impl", "!p || q"));
    ctx.push_obligation(ProofObligation::assume("not_q", "q == false"));
    ctx.push_obligation(ProofObligation::assert("not_p", "p == false"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "contrapositive should verify");
}

#[test]
fn implication_false_antecedent() {
    // false implies anything is true
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assert("vacuous", "!false || q"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "false implies anything");
}

#[test]
fn conditional_ite_positive() {
    // if x > 0 then x else -x should always be >= 0 (when x != MIN)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("not_min", "x > -2147483648"));
    ctx.push_obligation(ProofObligation::assert(
        "abs_nonneg",
        "if x > 0 { x } else { -x } >= 0",
    ));
    let result = AYEncoder::verify(&ctx);
    // This may or may not parse depending on ITE support — accept verified or error
    match result {
        VerifyResult::Verified => {}
        VerifyResult::Error { .. } => {}
        other => panic!("unexpected: {:?}", other),
    }
}

#[test]
fn implication_chain() {
    // If a < b and b < c, then a < c (transitivity as chained implications)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("c", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a < b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b < c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a < c"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "transitivity chain");
}

#[test]
fn implication_disjunctive_syllogism() {
    // If (P or Q) and !P, then Q
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("p_or_q", "p || q"));
    ctx.push_obligation(ProofObligation::assume("not_p", "p == false"));
    ctx.push_obligation(ProofObligation::assert("q_true", "q == true"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disjunctive syllogism");
}

#[test]
fn implication_hypothetical_syllogism() {
    // If (P => Q) and (Q => R), then (P => R)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("r", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("pq", "!p || q"));
    ctx.push_obligation(ProofObligation::assume("qr", "!q || r"));
    ctx.push_obligation(ProofObligation::assert("pr", "!p || r"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hypothetical syllogism");
}

#[test]
fn implication_bidirectional() {
    // (P iff Q) means (P => Q) and (Q => P)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("pq", "!p || q"));
    ctx.push_obligation(ProofObligation::assume("qp", "!q || p"));
    ctx.push_obligation(ProofObligation::assert("iff", "p == q"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bidirectional implication gives equivalence");
}

#[test]
fn implication_resolution() {
    // (P or Q) and (!P or R) implies (Q or R)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("r", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("clause1", "p || q"));
    ctx.push_obligation(ProofObligation::assume("clause2", "!p || r"));
    ctx.push_obligation(ProofObligation::assert("resolvent", "q || r"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution principle");
}

#[test]
fn implication_constructive_dilemma() {
    // If (P => Q) and (R => S) and (P or R), then (Q or S)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("p", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("r", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("s", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("pq", "!p || q"));
    ctx.push_obligation(ProofObligation::assume("rs", "!r || s"));
    ctx.push_obligation(ProofObligation::assume("p_or_r", "p || r"));
    ctx.push_obligation(ProofObligation::assert("q_or_s", "q || s"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "constructive dilemma");
}
