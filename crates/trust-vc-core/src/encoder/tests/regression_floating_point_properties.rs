// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sign_bit_positive() {
    // IEEE 754: sign bit 0 = positive
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sign_bit", u32_ty());
    ctx.declare_var_typed("is_positive", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sb", "sign_bit == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "pos_def",
        "is_positive == if sign_bit == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("positive", "is_positive == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign bit 0 → positive");
}

#[test]
fn sign_bit_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sign_bit", u32_ty());
    ctx.declare_var_typed("is_negative", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sb", "sign_bit == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "neg_def",
        "is_negative == if sign_bit == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("negative", "is_negative == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sign bit 1 → negative");
}

#[test]
fn exponent_bias_f32() {
    // IEEE 754 single: bias = 127, stored_exp = actual_exp + 127
    let mut ctx = VerificationContext::new();
    for v in &["actual_exp", "bias", "stored_exp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ae", "actual_exp == 3"));
    ctx.push_obligation(ProofObligation::assume("b", "bias == 127"));
    ctx.push_obligation(ProofObligation::assume(
        "se_def",
        "stored_exp == actual_exp + bias",
    ));
    ctx.push_obligation(ProofObligation::assert("is_130", "stored_exp == 130"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exp 3 + bias 127 = stored 130");
}

#[test]
fn denormalized_exponent_zero() {
    // Denormalized numbers have stored exponent = 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stored_exp", u32_ty());
    ctx.declare_var_typed("is_denorm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("se", "stored_exp == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "dn_def",
        "is_denorm == if stored_exp == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("denorm", "is_denorm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stored exp 0 → denormalized");
}

#[test]
fn infinity_exponent_all_ones() {
    // Infinity: exponent = 255 (all 1s for 8-bit), mantissa = 0
    let mut ctx = VerificationContext::new();
    for v in &["exponent", "mantissa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_inf", i32_ty());
    ctx.push_obligation(ProofObligation::assume("e", "exponent == 255"));
    ctx.push_obligation(ProofObligation::assume("m", "mantissa == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "inf_def",
        "is_inf == if exponent == 255 && mantissa == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_infinity", "is_inf == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exp=255, mantissa=0 → infinity");
}

#[test]
fn nan_exponent_all_ones_nonzero_mantissa() {
    // NaN: exponent = 255, mantissa != 0
    let mut ctx = VerificationContext::new();
    for v in &["exponent", "mantissa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("is_nan", i32_ty());
    ctx.push_obligation(ProofObligation::assume("e", "exponent == 255"));
    ctx.push_obligation(ProofObligation::assume("m", "mantissa == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "nan_def",
        "is_nan == if exponent == 255 && mantissa != 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_nan_val", "is_nan == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "exp=255, mantissa=1 → NaN");
}

#[test]
fn f32_bit_layout() {
    // 32 bits: 1 sign + 8 exponent + 23 mantissa
    let mut ctx = VerificationContext::new();
    for v in &["sign_bits", "exp_bits", "mantissa_bits", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "sign_bits == 1"));
    ctx.push_obligation(ProofObligation::assume("e", "exp_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("m", "mantissa_bits == 23"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == sign_bits + exp_bits + mantissa_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "total == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 + 8 + 23 = 32 bits");
}

#[test]
fn f64_bit_layout() {
    // 64 bits: 1 sign + 11 exponent + 52 mantissa
    let mut ctx = VerificationContext::new();
    for v in &["sign_bits", "exp_bits", "mantissa_bits", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "sign_bits == 1"));
    ctx.push_obligation(ProofObligation::assume("e", "exp_bits == 11"));
    ctx.push_obligation(ProofObligation::assume("m", "mantissa_bits == 52"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == sign_bits + exp_bits + mantissa_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_64", "total == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "1 + 11 + 52 = 64 bits");
}

#[test]
fn extract_sign_from_bits() {
    // Sign bit is the MSB: sign = (bits >> 31) & 1
    let mut ctx = VerificationContext::new();
    for v in &["bits", "sign"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 0x80000000 = 2147483648 (sign bit set, rest 0)
    ctx.push_obligation(ProofObligation::assume("b", "bits == 2147483648"));
    ctx.push_obligation(ProofObligation::assume("s_def", "sign == (bits >> 31) & 1"));
    ctx.push_obligation(ProofObligation::assert("is_1", "sign == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "extract sign from 0x80000000");
}

#[test]
fn zero_has_two_representations() {
    // +0 (sign=0) and -0 (sign=1) both have exponent=0, mantissa=0
    let mut ctx = VerificationContext::new();
    for v in &["pos_zero_sign", "neg_zero_sign", "exponent", "mantissa"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("pz", "pos_zero_sign == 0"));
    ctx.push_obligation(ProofObligation::assume("nz", "neg_zero_sign == 1"));
    ctx.push_obligation(ProofObligation::assume("e", "exponent == 0"));
    ctx.push_obligation(ProofObligation::assume("m", "mantissa == 0"));
    ctx.push_obligation(ProofObligation::assert(
        "diff_sign",
        "pos_zero_sign != neg_zero_sign",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "same_exp_mantissa",
        "exponent == 0 && mantissa == 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "+0 and -0 differ only in sign");
}
