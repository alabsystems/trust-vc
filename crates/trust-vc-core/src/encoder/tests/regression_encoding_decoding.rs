// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pack_unpack_two_bytes() {
    let mut ctx = VerificationContext::new();
    for v in &["hi", "lo", "packed", "hi2", "lo2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 171"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 205"));
    ctx.push_obligation(ProofObligation::assume(
        "packed_def",
        "packed == (hi << 8) | lo",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hi2_def",
        "hi2 == (packed >> 8) & 255",
    ));
    ctx.push_obligation(ProofObligation::assume("lo2_def", "lo2 == packed & 255"));
    ctx.push_obligation(ProofObligation::assert(
        "roundtrip",
        "hi2 == 171 && lo2 == 205",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pack(171, 205) then unpack roundtrips");
}

#[test]
fn encode_sign_magnitude() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "sign", "magnitude"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 42"));
    ctx.push_obligation(ProofObligation::assume(
        "sign_def",
        "sign == if x < 0 { 0 - 1 } else { 1 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "magnitude_def",
        "magnitude == if x < 0 { 0 - x } else { x }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "encoded",
        "sign == 0 - 1 && magnitude == 42",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "encode(-42) -> sign=-1, magnitude=42");
}

#[test]
fn decode_sign_magnitude() {
    let mut ctx = VerificationContext::new();
    for v in &["sign", "magnitude", "result"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("sign_val", "sign == 0 - 1"));
    ctx.push_obligation(ProofObligation::assume("magnitude_val", "magnitude == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == sign * magnitude",
    ));
    ctx.push_obligation(ProofObligation::assert("decoded", "result == 0 - 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "decode(sign=-1, mag=42) = -42");
}

#[test]
fn zigzag_encode() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "encoded"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    // Zigzag encoding: 0→0, -1→1, 1→2, -2→3, 2→4
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 0 - 2"));
    // zigzag(x) = (x << 1) ^ (x >> 31) for i32
    // For -2: (-2 << 1) = -4, (-2 >> 31) = -1, -4 ^ -1 = 3
    // We'll use the conditional form instead
    ctx.push_obligation(ProofObligation::assume(
        "encoded_def",
        "encoded == if x >= 0 { x + x } else { (0 - x) + (0 - x) - 1 }",
    ));
    ctx.push_obligation(ProofObligation::assert("zigzag", "encoded == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zigzag(-2) = 3");
}

#[test]
fn zigzag_decode() {
    let mut ctx = VerificationContext::new();
    for v in &["encoded", "decoded"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("encoded_val", "encoded == 3"));
    // zigzag decode: odd → -(n+1)/2, even → n/2
    ctx.push_obligation(ProofObligation::assume(
        "decoded_def",
        "decoded == if encoded % 2 == 0 { encoded / 2 } else { 0 - (encoded + 1) / 2 }",
    ));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "decoded == 0 - 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "zigzag_decode(3) = -2");
}

#[test]
fn bool_to_int_roundtrip() {
    let mut ctx = VerificationContext::new();
    for v in &["flag", "encoded", "decoded"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assume("encoded_def", "encoded == flag"));
    ctx.push_obligation(ProofObligation::assume(
        "decoded_def",
        "decoded == if encoded != 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "decoded == flag"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bool→int→bool roundtrip preserves value");
}

#[test]
fn pair_encoding() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "encoded", "a2", "b2"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= 0 && {v} <= 1000"),
        ));
    }
    // Cantor-like encoding for small pairs: encoded = a * 1000 + b
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "encoded_def",
        "encoded == a * 1000 + b",
    ));
    ctx.push_obligation(ProofObligation::assume("a2_def", "a2 == encoded / 1000"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == encoded % 1000"));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "a2 == 7 && b2 == 13"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pair encode/decode: (7,13) roundtrips");
}

#[test]
fn two_bit_field_pack() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "packed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Pack two 2-bit fields into one value
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 3"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "packed_def",
        "packed == (a << 2) | b",
    ));
    // 3 << 2 = 12, 12 | 2 = 14
    ctx.push_obligation(ProofObligation::assert("packed_val", "packed == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pack(3, 2) into 2-bit fields = 14");
}

#[test]
fn complement_encoding() {
    let mut ctx = VerificationContext::new();
    for v in &["x", "encoded", "decoded"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 42"));
    ctx.push_obligation(ProofObligation::assume("encoded_def", "encoded == x ^ 255"));
    ctx.push_obligation(ProofObligation::assume(
        "decoded_def",
        "decoded == encoded ^ 255",
    ));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "decoded == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR complement encoding roundtrips");
}

#[test]
fn offset_encoding() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "offset", "encoded", "decoded"] {
        ctx.declare_var_typed(v, i32_ty());
        ctx.push_obligation(ProofObligation::assume(
            format!("{v}_bound"),
            format!("{v} >= -10000 && {v} <= 10000"),
        ));
    }
    ctx.push_obligation(ProofObligation::assume("val_val", "val == 0 - 50"));
    ctx.push_obligation(ProofObligation::assume("offset_val", "offset == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "encoded_def",
        "encoded == val + offset",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "decoded_def",
        "decoded == encoded - offset",
    ));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "decoded == 0 - 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "offset encoding: -50 + 100 = 50, 50 - 100 = -50");
}
