// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ir::TrustVcType;
use crate::vc::ProofObligation;

#[test]
fn test_unit_literal_equality_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("unit_eq", "() == ()"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "unit literal should equal itself");
}

#[test]
fn test_unit_variable_is_singleton() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Unit);
    ctx.push_obligation(ProofObligation::assert("unit_var", "x == ()"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "unit variables should be constrained to ()");
}

#[test]
fn test_unit_returning_helper_function_is_singleton() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed(
        "make_unit",
        TrustVcType::Unit,
        vec![("n".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.push_obligation(ProofObligation::assert(
        "unit_fn_return",
        "make_unit(n) == ()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "unit-returning helper functions should produce the singleton unit value",
    );
}

#[test]
fn test_unit_quantifier_domain_is_singleton() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "unit_forall",
        "forall(|u: ()| u == ())",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "unit quantifier should range over only ()");
}
