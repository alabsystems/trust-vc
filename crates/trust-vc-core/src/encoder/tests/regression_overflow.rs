//! Overflow behavior regression tests.
//!
//! Verify that the encoder correctly detects overflows at type boundaries
//! and correctly allows in-range operations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn overflow_i32_add_positive_safe() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounded_a", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("bounded_a2", "a <= 1000000"));
    ctx.push_obligation(ProofObligation::assume("bounded_b", "b >= 0"));
    ctx.push_obligation(ProofObligation::assume("bounded_b2", "b <= 1000000"));
    ctx.push_obligation(ProofObligation::assert("safe", "a + b >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded positive add should not overflow");
}

#[test]
fn overflow_i32_add_max_overflows() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_max", "a == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "a + 1 > a"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "i32 MAX + 1 wraps to negative");
}

#[test]
fn overflow_i32_sub_min_overflows() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_min", "a == -2147483648"));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "a - 1 < a"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "i32 MIN - 1 wraps to positive");
}

#[test]
fn overflow_i32_mul_small_safe() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bounded_a", "a >= -100"));
    ctx.push_obligation(ProofObligation::assume("bounded_a2", "a <= 100"));
    ctx.push_obligation(ProofObligation::assume("bounded_b", "b >= -100"));
    ctx.push_obligation(ProofObligation::assume("bounded_b2", "b <= 100"));
    // The input bounds imply a product in -10000..=10000, which is wholly
    // inside i32. It is therefore sound to select the mathematical-integer
    // tactic explicitly instead of asking bit-blasting to certify this NIA
    // fact through a very large propositional proof.
    ctx.push_obligation(
        ProofObligation::assert("bounded_product", "a * b >= -10000")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "small product should be in range");

    ctx.push_obligation(ProofObligation::assume("a_at_upper_endpoint", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_at_upper_endpoint", "b == 100"));
    ctx.push_obligation(
        ProofObligation::assert("false_product_bound", "a * b < 10000")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );
    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "the nonlinear tactic must reject a strict bound on 100 * 100",
    );
}

#[test]
fn overflow_u32_sub_underflow() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "a - b < a"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "5 - 10 wraps for unsigned");
}

#[test]
fn overflow_u32_add_bounded_safe() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_bound", "a <= 2000000000"));
    ctx.push_obligation(ProofObligation::assume("b_bound", "b <= 2000000000"));
    ctx.push_obligation(ProofObligation::assert("safe", "a + b >= a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bounded u32 add does not wrap");
}

#[test]
fn overflow_i8_mul_boundary() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("is_min", "a == -128"));
    ctx.push_obligation(ProofObligation::assert("mul_neg", "a * -1 > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "-128 * -1 overflows i8");
}

#[test]
fn overflow_u8_add_max() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u8_ty());
    ctx.push_obligation(ProofObligation::assume("is_max", "a == 255"));
    ctx.push_obligation(ProofObligation::assert("wrap", "a + 1 > a"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "u8 255 + 1 wraps to 0");
}

#[test]
fn overflow_i32_neg_min() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_min", "a == -2147483648"));
    ctx.push_obligation(ProofObligation::assert("neg_pos", "-a > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "negation of MIN overflows");
}

#[test]
fn overflow_i32_shift_safe() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pos", "a == 1"));
    ctx.push_obligation(ProofObligation::assert("shift", "(a << 30) > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 << 30 is positive and in range");
}

#[test]
fn overflow_subtraction_same_sign() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_pos", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("b_pos", "b >= 0"));
    ctx.push_obligation(ProofObligation::assume("a_ge_b", "a >= b"));
    ctx.push_obligation(ProofObligation::assert("sub_nonneg", "a - b >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "positive a - positive b when a >= b is nonnegative",
    );
}

#[test]
fn overflow_u64_mul_boundary() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("b", u64_ty());
    ctx.push_obligation(ProofObligation::assume("a_large", "a == 4294967296"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 4294967296"));
    ctx.push_obligation(ProofObligation::assert("no_overflow", "a * b > a"));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "2^32 * 2^32 overflows u64");
}

#[test]
fn overflow_i32_division_safe() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 3"));
    ctx.push_obligation(ProofObligation::assert("div_bounded", "a / b >= 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "100 / 3 is a safe positive division");
}

#[test]
fn overflow_abs_safe_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_bound_lo", "a > -2147483648"));
    ctx.push_obligation(ProofObligation::assume("a_neg", "a < 0"));
    ctx.push_obligation(ProofObligation::assert("neg_pos", "-a > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "negating non-MIN negative value is positive");
}

#[test]
fn overflow_increment_from_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_neg", "a < 0"));
    ctx.push_obligation(ProofObligation::assert("closer_to_zero", "a + 1 > a"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "negative + 1 is closer to zero and cannot wrap");
}
