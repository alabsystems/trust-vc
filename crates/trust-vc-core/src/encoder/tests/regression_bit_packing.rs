// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn pack_two_u16_into_u32() {
    let mut ctx = VerificationContext::new();
    for v in &["hi", "lo", "packed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hi_val", "hi == 3"));
    ctx.push_obligation(ProofObligation::assume("lo_val", "lo == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "packed_def",
        "packed == (hi << 16) | lo",
    ));
    // 3 << 16 = 196608; 196608 | 7 = 196615
    ctx.push_obligation(ProofObligation::assert("is_packed", "packed == 196615"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pack (3, 7) into u32");
}

#[test]
fn unpack_hi_from_u32() {
    let mut ctx = VerificationContext::new();
    for v in &["packed", "hi"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("packed_val", "packed == 196615"));
    ctx.push_obligation(ProofObligation::assume("hi_def", "hi == packed >> 16"));
    ctx.push_obligation(ProofObligation::assert("hi_is_3", "hi == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "unpack hi from 196615 = 3");
}

#[test]
fn unpack_lo_from_u32() {
    let mut ctx = VerificationContext::new();
    for v in &["packed", "lo"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("packed_val", "packed == 196615"));
    ctx.push_obligation(ProofObligation::assume("lo_def", "lo == packed & 65535"));
    ctx.push_obligation(ProofObligation::assert("lo_is_7", "lo == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "unpack lo from 196615 = 7");
}

#[test]
fn pack_four_u8_into_u32() {
    let mut ctx = VerificationContext::new();
    for v in &["b3", "b2", "b1", "b0", "packed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b3_val", "b3 == 1"));
    ctx.push_obligation(ProofObligation::assume("b2_val", "b2 == 2"));
    ctx.push_obligation(ProofObligation::assume("b1_val", "b1 == 3"));
    ctx.push_obligation(ProofObligation::assume("b0_val", "b0 == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "packed_def",
        "packed == (b3 << 24) | (b2 << 16) | (b1 << 8) | b0",
    ));
    // 1*16777216 + 2*65536 + 3*256 + 4 = 16909060
    ctx.push_obligation(ProofObligation::assert("is_packed", "packed == 16909060"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pack [1,2,3,4] into u32");
}

#[test]
fn extract_byte_from_packed() {
    let mut ctx = VerificationContext::new();
    for v in &["packed", "byte1"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("packed_val", "packed == 16909060"));
    // Extract byte 1 (bits 8-15): (packed >> 8) & 0xFF
    ctx.push_obligation(ProofObligation::assume(
        "byte1_def",
        "byte1 == (packed >> 8) & 255",
    ));
    ctx.push_obligation(ProofObligation::assert("is_3", "byte1 == 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "extract byte 1 from packed = 3");
}

#[test]
fn set_bit_field() {
    // Set bits 4-7 of a u32 to a 4-bit value
    let mut ctx = VerificationContext::new();
    for v in &["original", "field_val", "mask", "cleared", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("orig", "original == 255"));
    ctx.push_obligation(ProofObligation::assume("field", "field_val == 10"));
    // mask = ~(0xF << 4) = ~0xF0 = 0xFFFFFF0F = 4294967055
    ctx.push_obligation(ProofObligation::assume("mask_val", "mask == 4294967055"));
    ctx.push_obligation(ProofObligation::assume(
        "clear_def",
        "cleared == original & mask",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == cleared | (field_val << 4)",
    ));
    // original = 0xFF, clear bits 4-7: 0x0F, set to 0xA0: 0xAF = 175
    ctx.push_obligation(ProofObligation::assert("is_175", "result == 175"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "set 4-bit field in u32");
}

#[test]
fn rgb_pack_unpack() {
    // Pack RGB (8-bit each) into u32, unpack green
    let mut ctx = VerificationContext::new();
    for v in &["r", "g", "b", "packed", "extracted_g"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 255"));
    ctx.push_obligation(ProofObligation::assume("g_val", "g == 128"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "packed_def",
        "packed == (r << 16) | (g << 8) | b",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "extract_g",
        "extracted_g == (packed >> 8) & 255",
    ));
    ctx.push_obligation(ProofObligation::assert("g_roundtrip", "extracted_g == 128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "RGB pack/unpack green channel");
}

#[test]
fn flag_word_set_and_test() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "with_bit3", "has_bit3"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 0"));
    ctx.push_obligation(ProofObligation::assume("set_def", "with_bit3 == flags | 8"));
    ctx.push_obligation(ProofObligation::assume(
        "test_def",
        "has_bit3 == (with_bit3 >> 3) & 1",
    ));
    ctx.push_obligation(ProofObligation::assert("bit_set", "has_bit3 == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "set bit 3 then test it");
}

#[test]
fn pack_unpack_roundtrip_u16() {
    // Pack two u16 and unpack, verify roundtrip
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "packed", "out_a", "out_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 100"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "packed_def",
        "packed == (a << 16) | b",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "out_a_def",
        "out_a == packed >> 16",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "out_b_def",
        "out_b == packed & 65535",
    ));
    ctx.push_obligation(ProofObligation::assert("a_roundtrip", "out_a == 100"));
    ctx.push_obligation(ProofObligation::assert("b_roundtrip", "out_b == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pack/unpack u16 pair roundtrip");
}

#[test]
fn nibble_swap() {
    // Swap low and high nibbles of a byte
    let mut ctx = VerificationContext::new();
    for v in &["byte_val", "lo", "hi", "swapped"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("byte", "byte_val == 171"));
    // 0xAB: lo = 0xB = 11, hi = 0xA = 10
    ctx.push_obligation(ProofObligation::assume("lo_def", "lo == byte_val & 15"));
    ctx.push_obligation(ProofObligation::assume(
        "hi_def",
        "hi == (byte_val >> 4) & 15",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "swap_def",
        "swapped == (lo << 4) | hi",
    ));
    // swapped = 0xBA = 186
    ctx.push_obligation(ProofObligation::assert("is_186", "swapped == 186"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "swap nibbles of 0xAB = 0xBA");
}
