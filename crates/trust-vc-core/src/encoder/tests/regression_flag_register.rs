// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn set_single_bit() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 0"));
    ctx.push_obligation(ProofObligation::assume("result_def", "result == flags | 4"));
    ctx.push_obligation(ProofObligation::assert("bit_set", "result == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "set bit 2: 0 | 4 = 4");
}

#[test]
fn clear_single_bit() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "mask", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 7"));
    // Clear bit 1: 7 & ~2 = 7 & (0xFFFFFFFF ^ 2) = 5
    // Since we can't use ~ easily, we use XOR to flip
    ctx.push_obligation(ProofObligation::assume(
        "mask_def",
        "mask == 4294967295 ^ 2",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == flags & mask",
    ));
    ctx.push_obligation(ProofObligation::assert("bit_cleared", "result == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "clear bit 1: 7 & ~2 = 5");
}

#[test]
fn test_bit_set() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "test_result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "test_def",
        "test_result == flags & 4",
    ));
    ctx.push_obligation(ProofObligation::assert("bit_is_set", "test_result != 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bit 2 of 5 (0b101) is set");
}

#[test]
fn test_bit_clear() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "test_result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "test_def",
        "test_result == flags & 2",
    ));
    ctx.push_obligation(ProofObligation::assert("bit_is_clear", "test_result == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bit 1 of 5 (0b101) is clear");
}

#[test]
fn toggle_bit() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "toggled"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "toggled_def",
        "toggled == flags ^ 2",
    ));
    // 5 = 0b101, toggle bit 1 → 0b111 = 7
    ctx.push_obligation(ProofObligation::assert("toggled_val", "toggled == 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "toggle bit 1: 5 ^ 2 = 7");
}

#[test]
fn toggle_twice_is_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "once", "twice"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 10"));
    ctx.push_obligation(ProofObligation::assume("once_def", "once == flags ^ 4"));
    ctx.push_obligation(ProofObligation::assume("twice_def", "twice == once ^ 4"));
    ctx.push_obligation(ProofObligation::assert("identity", "twice == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "double XOR toggle is identity");
}

#[test]
fn set_multiple_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 0"));
    // Set bits 0, 2, 4 → 1 + 4 + 16 = 21
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "result == flags | 21",
    ));
    ctx.push_obligation(ProofObligation::assert("multi_set", "result == 21"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "set bits 0,2,4: 0 | 21 = 21");
}

#[test]
fn or_idempotent() {
    let mut ctx = VerificationContext::new();
    for v in &["flags", "once", "twice"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("flags_val", "flags == 3"));
    ctx.push_obligation(ProofObligation::assume("once_def", "once == flags | 8"));
    ctx.push_obligation(ProofObligation::assume("twice_def", "twice == once | 8"));
    ctx.push_obligation(ProofObligation::assert("idempotent", "twice == once"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "OR is idempotent: setting bit twice = once");
}

#[test]
fn count_set_bits_nibble() {
    // Count set bits of 0b1010 = 10 → 2 bits set
    let mut ctx = VerificationContext::new();
    for v in &["x", "b0", "b1", "b2", "b3", "count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 10"));
    ctx.push_obligation(ProofObligation::assume("b0_def", "b0 == x & 1"));
    ctx.push_obligation(ProofObligation::assume("b1_def", "b1 == (x >> 1) & 1"));
    ctx.push_obligation(ProofObligation::assume("b2_def", "b2 == (x >> 2) & 1"));
    ctx.push_obligation(ProofObligation::assume("b3_def", "b3 == (x >> 3) & 1"));
    ctx.push_obligation(ProofObligation::assume(
        "count_def",
        "count == b0 + b1 + b2 + b3",
    ));
    ctx.push_obligation(ProofObligation::assert("two_bits", "count == 2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "popcount of 0b1010 = 2");
}

#[test]
fn extract_field() {
    let mut ctx = VerificationContext::new();
    for v in &["reg", "field"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Extract bits [5:3] from reg = 0b11101000 = 232
    // (reg >> 3) & 0b111 = (232 >> 3) & 7 = 29 & 7 = 5
    ctx.push_obligation(ProofObligation::assume("reg_val", "reg == 232"));
    ctx.push_obligation(ProofObligation::assume(
        "field_def",
        "field == (reg >> 3) & 7",
    ));
    ctx.push_obligation(ProofObligation::assert("extracted", "field == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "extract bits [5:3] from 232 = 5");
}
