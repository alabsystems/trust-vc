// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn fixed_point_add() {
    // Fixed-point Q8.8: value * 256 stored as integer
    // 1.5 + 2.25 = 3.75 → 384 + 576 = 960
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 384"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 576"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == a + b"));
    ctx.push_obligation(ProofObligation::assert("is_960", "sum == 960"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Q8.8: 1.5 + 2.25 = 3.75 (384 + 576 = 960)");
}

#[test]
fn fixed_point_sub() {
    // 3.0 - 1.5 = 1.5 → 768 - 384 = 384
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "diff"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 768"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 384"));
    ctx.push_obligation(ProofObligation::assume("diff_def", "diff == a - b"));
    ctx.push_obligation(ProofObligation::assert("is_384", "diff == 384"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Q8.8: 3.0 - 1.5 = 1.5 (768 - 384 = 384)");
}

#[test]
fn fixed_point_mul_scaled() {
    // Fixed-point multiply: (a * b) >> 8 to rescale
    // 2.0 * 3.0 = 6.0 → (512 * 768) >> 8 = 393216 >> 8 = 1536
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "product_raw", "product"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 512"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 768"));
    ctx.push_obligation(ProofObligation::assume("prod_raw", "product_raw == a * b"));
    ctx.push_obligation(ProofObligation::assume(
        "prod_def",
        "product == product_raw >> 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1536", "product == 1536"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Q8.8: 2.0 * 3.0 = 6.0 (rescaled)");
}

#[test]
fn fixed_point_integer_part() {
    // Extract integer part: value >> 8
    // 2.75 = 704 in Q8.8; integer part = 704 >> 8 = 2
    let mut ctx = VerificationContext::new();
    for v in &["value", "int_part"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("val", "value == 704"));
    ctx.push_obligation(ProofObligation::assume("int_def", "int_part == value >> 8"));
    ctx.push_obligation(ProofObligation::assert("is_2", "int_part == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Q8.8: integer part of 2.75 = 2");
}

#[test]
fn fixed_point_fractional_part() {
    // Extract fractional part: value & 0xFF
    // 2.75 = 704; fractional = 704 & 255 = 192 (0.75 * 256 = 192)
    let mut ctx = VerificationContext::new();
    for v in &["value", "frac_part"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("val", "value == 704"));
    ctx.push_obligation(ProofObligation::assume(
        "frac_def",
        "frac_part == value & 255",
    ));
    ctx.push_obligation(ProofObligation::assert("is_192", "frac_part == 192"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Q8.8: fractional part of 2.75 = 192/256");
}

#[test]
fn fixed_point_from_integer() {
    // Convert integer 5 to Q8.8: 5 << 8 = 1280
    let mut ctx = VerificationContext::new();
    for v in &["int_val", "fixed_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("int", "int_val == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "fixed_def",
        "fixed_val == int_val << 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1280", "fixed_val == 1280"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Q8.8: integer 5 → fixed 1280");
}

#[test]
fn fixed_point_round_to_integer() {
    // Round to nearest integer: (value + 128) >> 8
    // 2.75 = 704; (704 + 128) >> 8 = 832 >> 8 = 3
    let mut ctx = VerificationContext::new();
    for v in &["value", "rounded"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("val", "value == 704"));
    ctx.push_obligation(ProofObligation::assume(
        "round_def",
        "rounded == (value + 128) >> 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "rounded == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "Q8.8: round 2.75 → 3");
}

#[test]
fn fixed_point_add_commutative() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "sum_ab", "sum_ba"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 384"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 576"));
    ctx.push_obligation(ProofObligation::assume("sum_ab_def", "sum_ab == a + b"));
    ctx.push_obligation(ProofObligation::assume("sum_ba_def", "sum_ba == b + a"));
    ctx.push_obligation(ProofObligation::assert("commutative", "sum_ab == sum_ba"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Q8.8 addition is commutative");
}

#[test]
fn fixed_point_negate() {
    // Negate in Q8.8: two's complement
    // 1.5 = 384 → -1.5 = 2^32 - 384 = 4294966912
    let mut ctx = VerificationContext::new();
    for v in &["value", "negated", "sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("val", "value == 384"));
    ctx.push_obligation(ProofObligation::assume("neg_def", "negated == 0 - value"));
    ctx.push_obligation(ProofObligation::assume("sum_def", "sum == value + negated"));
    // wrapping: 384 + (2^32 - 384) = 2^32 = 0 mod 2^32
    ctx.push_obligation(ProofObligation::assert("cancels", "sum == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Q8.8: value + (-value) = 0");
}

#[test]
fn fixed_point_comparison() {
    // 1.5 < 2.25 in Q8.8: 384 < 576
    let mut ctx = VerificationContext::new();
    for v in &["a", "b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 384"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 576"));
    ctx.push_obligation(ProofObligation::assert("a_lt_b", "a < b"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Q8.8: 1.5 < 2.25 ↔ 384 < 576");
}
