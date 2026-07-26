// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn swap_bytes_u16() {
    // 0x1234 → 0x3412
    let mut ctx = VerificationContext::new();
    for v in &["val", "lo", "hi", "swapped"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 4660")); // 0x1234
    ctx.push_obligation(ProofObligation::assume("lo_def", "lo == val & 255"));
    ctx.push_obligation(ProofObligation::assume("hi_def", "hi == (val >> 8) & 255"));
    ctx.push_obligation(ProofObligation::assume(
        "sw_def",
        "swapped == (lo << 8) | hi",
    ));
    ctx.push_obligation(ProofObligation::assert("is_0x3412", "swapped == 13330"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "swap_bytes(0x1234) = 0x3412");
}

#[test]
fn extract_byte_0() {
    // Byte 0 (least significant) of 0xDEADBEEF
    let mut ctx = VerificationContext::new();
    for v in &["val", "byte0"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 3735928559")); // 0xDEADBEEF
    ctx.push_obligation(ProofObligation::assume("b0_def", "byte0 == val & 255"));
    // 0xEF = 239
    ctx.push_obligation(ProofObligation::assert("is_0xEF", "byte0 == 239"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "byte 0 of 0xDEADBEEF = 0xEF");
}

#[test]
fn extract_byte_1() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "byte1"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 3735928559")); // 0xDEADBEEF
    ctx.push_obligation(ProofObligation::assume(
        "b1_def",
        "byte1 == (val >> 8) & 255",
    ));
    // 0xBE = 190
    ctx.push_obligation(ProofObligation::assert("is_0xBE", "byte1 == 190"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "byte 1 of 0xDEADBEEF = 0xBE");
}

#[test]
fn big_endian_first_byte_is_msb() {
    // Big endian: first byte = most significant
    let mut ctx = VerificationContext::new();
    for v in &["value", "first_byte"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "value == 4660")); // 0x1234
    ctx.push_obligation(ProofObligation::assume(
        "fb_def",
        "first_byte == (value >> 8) & 255",
    ));
    // MSB of 0x1234 is 0x12 = 18
    ctx.push_obligation(ProofObligation::assert("is_0x12", "first_byte == 18"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "big endian: first byte = 0x12");
}

#[test]
fn little_endian_first_byte_is_lsb() {
    let mut ctx = VerificationContext::new();
    for v in &["value", "first_byte"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "value == 4660")); // 0x1234
    ctx.push_obligation(ProofObligation::assume(
        "fb_def",
        "first_byte == value & 255",
    ));
    // LSB of 0x1234 is 0x34 = 52
    ctx.push_obligation(ProofObligation::assert("is_0x34", "first_byte == 52"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "little endian: first byte = 0x34");
}

#[test]
fn roundtrip_swap() {
    // swap(swap(x)) == x for 16-bit
    let mut ctx = VerificationContext::new();
    for v in &["val", "lo1", "hi1", "swap1", "lo2", "hi2", "swap2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 4660"));
    ctx.push_obligation(ProofObligation::assume("lo1_def", "lo1 == val & 255"));
    ctx.push_obligation(ProofObligation::assume(
        "hi1_def",
        "hi1 == (val >> 8) & 255",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s1_def",
        "swap1 == (lo1 << 8) | hi1",
    ));
    ctx.push_obligation(ProofObligation::assume("lo2_def", "lo2 == swap1 & 255"));
    ctx.push_obligation(ProofObligation::assume(
        "hi2_def",
        "hi2 == (swap1 >> 8) & 255",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "s2_def",
        "swap2 == (lo2 << 8) | hi2",
    ));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "swap2 == val"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "swap(swap(0x1234)) = 0x1234");
}

#[test]
fn network_byte_order_is_big_endian() {
    // Network order = big endian; htons(0x0050) for port 80
    let mut ctx = VerificationContext::new();
    for v in &["host_port", "net_lo", "net_hi", "net_port"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("hp", "host_port == 80")); // 0x0050
    ctx.push_obligation(ProofObligation::assume(
        "nl_def",
        "net_lo == host_port & 255",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nh_def",
        "net_hi == (host_port >> 8) & 255",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "np_def",
        "net_port == (net_lo << 8) | net_hi",
    ));
    // 80 = 0x0050: lo=0x50=80, hi=0x00=0; swapped = 80*256 + 0 = 20480 = 0x5000
    ctx.push_obligation(ProofObligation::assert("is_20480", "net_port == 20480"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "htons(80) = 20480");
}

#[test]
fn mask_preserves_byte_range() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "masked"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 300"));
    ctx.push_obligation(ProofObligation::assume("m_def", "masked == val & 255"));
    ctx.push_obligation(ProofObligation::assert("in_byte", "masked < 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "val & 0xFF < 256");
}

#[test]
fn combine_two_bytes() {
    // Combine hi=0xAB, lo=0xCD → 0xABCD
    let mut ctx = VerificationContext::new();
    for v in &["hi", "lo", "combined"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hi == 171")); // 0xAB
    ctx.push_obligation(ProofObligation::assume("l", "lo == 205")); // 0xCD
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "combined == (hi << 8) | lo",
    ));
    // 171*256 + 205 = 43981 = 0xABCD
    ctx.push_obligation(ProofObligation::assert("is_0xABCD", "combined == 43981"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0xAB << 8 | 0xCD = 0xABCD");
}

#[test]
fn byte_order_does_not_change_value_interpretation() {
    // Same numeric value regardless of storage order
    let mut ctx = VerificationContext::new();
    for v in &["value_be", "value_le"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("be", "value_be == 4660"));
    ctx.push_obligation(ProofObligation::assume("le", "value_le == 4660"));
    ctx.push_obligation(ProofObligation::assert(
        "same_value",
        "value_be == value_le",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "same logical value in both byte orders");
}
