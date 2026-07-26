//! Quantifier encoding regression tests.
//!
//! Verify that forall and exists quantifiers encode and solve correctly.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn register_int_predicate(ctx: &mut VerificationContext, name: &str) {
    ctx.set_function_context(crate::vc::FunctionContext {
        name: name.to_string(),
        params: vec![("i".to_string(), crate::ir::TrustVcType::MathInt)],
        return_type: crate::ir::TrustVcType::Bool,
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
}

#[test]
fn quantifier_trivial_forall_true() {
    // forall x: i32. true — should verify
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("trivial", "forall(|x: i32| true)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forall x. true should verify");
}

#[test]
fn quantifier_trivial_forall_false() {
    // forall x: i32. false — should find counterexample
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "impossible",
        "forall(|x: i32| false)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "forall x. false is unsatisfiable");
}

#[test]
fn quantifier_exists_witness() {
    // exists x: i32. x == 42 — should verify (42 is a valid i32)
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "witness",
        "exists(|x: i32| x == 42)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "there exists an i32 equal to 42");
}

#[test]
fn quantifier_forall_bounded() {
    // forall x: i32. x >= 0 && x <= 10 ==> x < 100
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "forall(|x: i32| !(x >= 0 && x <= 10) || x < 100)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded forall should verify");
}

#[test]
fn quantifier_forall_unbounded_false() {
    // forall x: i32. x > 0 — false (x can be 0 or negative)
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("all_pos", "forall(|x: i32| x > 0)"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "not all i32 are positive");
}

#[test]
fn quantifier_nested_exists_forall() {
    // This tests that nested quantifiers encode correctly.
    // exists y: i32. forall x: i32. !(x == y) || x == y
    // Simplified: exists y. forall x. x != y || x == y — tautology
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "nested",
        "exists(|y: i32| forall(|x: i32| !(x == y) || x == y))",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "tautological nested quantifier");
}

#[test]
fn quantifier_forall_with_assumption() {
    // Assume a is positive, then assert it remains positive.
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_pos", "a > 0"));
    ctx.push_obligation(ProofObligation::assert("still_pos", "a > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "assumption propagates to assertion");
}

#[test]
fn quantifier_exists_no_witness() {
    // exists x: u8. x > 255 — impossible
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "impossible",
        "exists(|x: u8| x > 255)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "no u8 exceeds 255");
}

#[test]
fn quantifier_upstream_test1_fails_u32_max_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "u32_exists_above_max",
        "exists(|i: u32| i > 0xffff_ffffu32)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "no u32 exceeds u32::MAX");
}

#[test]
fn quantifier_forall_reflexive_eq() {
    // forall x: i32. x == x — always true
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("refl", "forall(|x: i32| x == x)"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reflexive equality is always true");
}

#[test]
fn quantifier_multiple_vars() {
    // forall x y: i32. !(x == y) || y == x — symmetry of equality
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "sym",
        "forall(|x: i32, y: i32| !(x == y) || y == x)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equality is symmetric");
}

#[test]
fn quantifier_upstream_test1_exists_uses_ground_predicate_fact() {
    // Upstream quantifiers.rs::test1 shape:
    //   tr(300); assert exists |i: nat| i >= 0 && tr(i as int)
    //
    // The ground fact is modeled as an assumption here because this regression
    // isolates quantifier/trigger behavior, not spec-function transparency.
    let mut ctx = VerificationContext::new();
    register_int_predicate(&mut ctx, "tr");
    ctx.push_obligation(ProofObligation::assume("tr_300", "tr(300)"));
    ctx.push_obligation(ProofObligation::assert(
        "exists_nat_witness_from_ground_fact",
        "exists(|i: nat| i >= 0 && tr(i as int))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ground tr(300) should prove exists(|i: nat| i >= 0 && tr(i as int))",
    );
}

#[test]
fn quantifier_upstream_test1_fails_without_ground_predicate_fact() {
    // Upstream quantifiers.rs::test1_fails shape: without a matching ground
    // predicate fact, the existential over an uninterpreted predicate must not
    // verify.
    let mut ctx = VerificationContext::new();
    register_int_predicate(&mut ctx, "tr");
    ctx.push_obligation(ProofObligation::assert(
        "exists_nat_witness_without_ground_fact",
        "exists(|i: nat| i >= 0 && tr(i as int))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "exists(|i: nat| i >= 0 && tr(i as int)) must fail closed without a ground tr fact",
    );
}

#[test]
fn quantifier_ground_predicate_fact_rejects_dual_forall_negation() {
    // Existential support must line up with the forall dual: once tr(300) is
    // known, forall nat i. !tr(i as int) is false.
    let mut ctx = VerificationContext::new();
    register_int_predicate(&mut ctx, "tr");
    ctx.push_obligation(ProofObligation::assume("tr_300", "tr(300)"));
    ctx.push_obligation(ProofObligation::assert(
        "forall_not_tr_rejected",
        "forall(|i: nat| !tr(i as int))",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall(|i: nat| !tr(i as int)) must not verify when tr(300) is known",
    );
}
