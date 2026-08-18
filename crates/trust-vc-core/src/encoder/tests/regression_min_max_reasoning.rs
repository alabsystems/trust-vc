// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn max_ge_both() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "m == if a >= b { a } else { b }",
    ));
    // The explicit arithmetic tactic uses mathematical integers. `m` only
    // selects one of two values in -1000..=1000, so that interpretation is
    // equivalent to i32 execution here.
    ctx.push_obligation(
        ProofObligation::assert("max_ge_both", "m >= a && m >= b")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max should be greater than or equal to both inputs",
    );

    // Keep the explicit tactic honest at a branch-selecting endpoint.
    ctx.push_obligation(ProofObligation::assume("a_at_lower_endpoint", "a == -1000"));
    ctx.push_obligation(ProofObligation::assume("b_at_upper_endpoint", "b == 1000"));
    ctx.push_obligation(
        ProofObligation::assert("false_max_bound", "m < b")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "the nonlinear tactic must reject a strict bound on max(-1000, 1000)",
    );
}

#[test]
fn min_le_both() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.declare_var_typed("m", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "m_def",
        "m == if a <= b { a } else { b }",
    ));
    // As above, all possible selected values are far inside i32, making the
    // explicit mathematical-integer tactic equivalent to machine execution.
    ctx.push_obligation(
        ProofObligation::assert("min_le_both", "m <= a && m <= b")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min should be less than or equal to both inputs");

    ctx.push_obligation(ProofObligation::assume("a_at_lower_endpoint", "a == -1000"));
    ctx.push_obligation(ProofObligation::assume("b_at_upper_endpoint", "b == 1000"));
    ctx.push_obligation(
        ProofObligation::assert("false_min_bound", "m > a")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "the nonlinear tactic must reject a strict bound on min(-1000, 1000)",
    );
}

#[test]
fn max_is_one_of() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "max_is_one_of",
        "(if a >= b { a } else { b } == a) || (if a >= b { a } else { b } == b)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max should equal one of its inputs");
}

#[test]
fn min_is_one_of() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_min", "a >= -1000"));
    ctx.push_obligation(ProofObligation::assume("a_max", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assume("b_min", "b >= -1000"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "min_is_one_of",
        "(if a <= b { a } else { b } == a) || (if a <= b { a } else { b } == b)",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min should equal one of its inputs");
}

#[test]
fn max_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "max_commutative",
        "if a >= b { a } else { b } == if b >= a { b } else { a }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max should be commutative for concrete inputs");
}

#[test]
fn min_commutative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "min_commutative",
        "if a <= b { a } else { b } == if b <= a { b } else { a }",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min should be commutative for concrete inputs");
}

#[test]
fn max_of_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "max_of_equal",
        "if a >= b { a } else { b } == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max of equal values should be that value");
}

#[test]
fn min_of_equal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "min_of_equal",
        "if a <= b { a } else { b } == 5",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min of equal values should be that value");
}

#[test]
fn max_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_lower", "a >= 1"));
    ctx.push_obligation(ProofObligation::assume("a_upper", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "max_positive",
        "if a >= 0 { a } else { 0 } == a",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max with zero should preserve a positive value");
}

#[test]
fn min_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_lower", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("a_upper", "a <= 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "min_nonneg",
        "if a <= 0 { a } else { 0 } == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "min with zero should be zero for nonnegative inputs",
    );
}
