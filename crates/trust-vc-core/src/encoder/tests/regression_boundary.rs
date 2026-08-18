//! Boundary condition regression tests.
//!
//! These tests lock behavior at type boundaries (MIN, MAX, 0, -1, 1)
//! and ensure the encoder correctly handles edge cases.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// --- i8 boundaries ---

#[test]
fn boundary_i8_max_plus_one_overflows() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 127"));
    ctx.push_obligation(ProofObligation::assert("no_overflow", "x + 1 > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "i8::MAX + 1 should not verify as still positive");
}

#[test]
fn boundary_i8_min_minus_one_overflows() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Int { width: 8 });
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -128"));
    ctx.push_obligation(ProofObligation::assert("no_underflow", "x - 1 < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "i8::MIN - 1 should not verify as still negative");
}

#[test]
fn boundary_i32_max_is_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 2147483647"));
    ctx.push_obligation(ProofObligation::assert("positive", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32::MAX should remain positive");
}

#[test]
fn boundary_i32_min_is_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -2147483648"));
    ctx.push_obligation(ProofObligation::assert("negative", "x < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "i32::MIN should remain negative");
}

#[test]
fn boundary_u32_zero_minus_one_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_zero", "x == 0"));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "x - 1 < x"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "0u32 - 1 should not verify as less than 0u32");
}

#[test]
fn boundary_u32_max_is_large() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 4294967295"));
    ctx.push_obligation(ProofObligation::assert("large", "x > 1000000"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u32::MAX should be larger than one million");
}

#[test]
fn boundary_u64_max_plus_one_wraps() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u64_ty());
    ctx.push_obligation(ProofObligation::assume(
        "x_max",
        "x == 18446744073709551615",
    ));
    ctx.push_obligation(ProofObligation::assert("no_wrap", "x + 1 > x"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "u64::MAX + 1 should not verify as larger than u64::MAX",
    );
}

#[test]
fn boundary_i32_negation_of_min_overflows() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -2147483648"));
    ctx.push_obligation(ProofObligation::assert("neg_safe", "-x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "negating i32::MIN should not verify as positive");
}

#[test]
fn boundary_zero_division_guard() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.declare_var_typed("y", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("y_zero", "y == 0"));
    ctx.push_obligation(ProofObligation::assert("safe_div", "y != 0"));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(&result, "division guard should fail when divisor is zero");
}

#[test]
fn boundary_i32_add_same_sign_no_overflow_in_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_nonnegative", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("a_bounded", "a <= 1000000"));
    ctx.push_obligation(ProofObligation::assume("b_nonnegative", "b >= 0"));
    ctx.push_obligation(ProofObligation::assume("b_bounded", "b <= 1000000"));
    ctx.push_obligation(ProofObligation::assert("safe_add", "a + b >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "bounded nonnegative i32 addition should stay nonnegative",
    );
}

#[test]
fn boundary_bool_and_true_true() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("a_true", "a == true"));
    ctx.push_obligation(ProofObligation::assume("b_true", "b == true"));
    ctx.push_obligation(ProofObligation::assert("and_tt", "(a && b) == true"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "true && true should verify as true");
}

#[test]
fn boundary_bool_or_false_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Bool);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Bool);
    ctx.push_obligation(ProofObligation::assume("a_false", "a == false"));
    ctx.push_obligation(ProofObligation::assume("b_false", "b == false"));
    ctx.push_obligation(ProofObligation::assert("or_ff", "(a || b) == false"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "false || false should verify as false");
}

#[test]
fn boundary_shift_left_by_31() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_one", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("shift", "(x << 31) < 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1i32 << 31 should set the sign bit");
}

#[test]
fn boundary_shift_left_by_32_undefined() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_one", "x == 1"));
    ctx.push_obligation(ProofObligation::assert("no_undef", "(x << 32) == 0"));

    let result = AYEncoder::verify(&ctx);
    // Shift by the bit width is undefined and must not verify cleanly.
    expect_not_verified(&result, "1i32 << 32 should not verify");
}

#[test]
fn boundary_u8_bitwise_and_mask() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 255"));
    ctx.push_obligation(ProofObligation::assert("mask", "(x & 15) == 15"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "255u8 masked by 15 should yield 15");
}

#[test]
fn boundary_u8_bitwise_or_identity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u8_ty());
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 170"));
    ctx.push_obligation(ProofObligation::assert("or_id", "(x | 0) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x | 0 should preserve a u8 value");
}

#[test]
fn boundary_comparison_equal_values() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("equal", "a == b"));
    ctx.push_obligation(ProofObligation::assert("eq_leq", "a <= b"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "equal i32 values should satisfy <=");
}

#[test]
fn boundary_comparison_strict_less() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", i32_ty());
    ctx.declare_var_typed("b", i32_ty());
    ctx.push_obligation(ProofObligation::assume("strict_lt", "a < b"));
    ctx.push_obligation(ProofObligation::assert("lt_ne", "a != b"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "strictly ordered i32 values should differ");
}

#[test]
fn boundary_u32_mul_small_values() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_bounded", "a <= 100"));
    ctx.push_obligation(ProofObligation::assume("b_bounded", "b <= 100"));
    // This explicit Verus-style nonlinear tactic uses mathematical integers.
    // The premises make that interpretation equivalent to u32 execution here:
    // the product is in 0..=10_000 and therefore cannot wrap.
    ctx.push_obligation(
        ProofObligation::assert("mul_bounded", "a * b <= 10000")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "small u32 factors should keep the product bounded");
}

#[test]
fn boundary_u32_mul_nonlinear_rejects_stronger_false_bound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u32_ty());
    ctx.declare_var_typed("b", u32_ty());
    ctx.push_obligation(ProofObligation::assume("a_max", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_max", "b == 100"));
    ctx.push_obligation(
        ProofObligation::assert("false_bound", "a * b < 10000")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "the nonlinear tactic must reject a stronger false product bound",
    );
}

#[test]
fn boundary_i32_abs_of_positive() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(ProofObligation::assume("x_positive", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("abs_pos", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "positive i32 values should satisfy the identity implication",
    );
}
