// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn add_two_registers() {
    let mut ctx = VerificationContext::new();
    for v in &["rs1", "rs2", "rd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r1", "rs1 == 10"));
    ctx.push_obligation(ProofObligation::assume("r2", "rs2 == 20"));
    ctx.push_obligation(ProofObligation::assume("rd_def", "rd == rs1 + rs2"));
    ctx.push_obligation(ProofObligation::assert("is_30", "rd == 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADD: 10 + 20 = 30");
}

#[test]
fn sub_two_registers() {
    let mut ctx = VerificationContext::new();
    for v in &["rs1", "rs2", "rd"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r1", "rs1 == 50"));
    ctx.push_obligation(ProofObligation::assume("r2", "rs2 == 30"));
    ctx.push_obligation(ProofObligation::assume("rd_def", "rd == rs1 - rs2"));
    ctx.push_obligation(ProofObligation::assert("is_20", "rd == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SUB: 50 - 30 = 20");
}

#[test]
fn and_operation() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 15"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 9"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == a & b"));
    // 15 = 1111, 9 = 1001, AND = 1001 = 9
    ctx.push_obligation(ProofObligation::assert("is_9", "result == 9"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "AND: 15 & 9 = 9");
}

#[test]
fn or_operation() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 10"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 5"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == a | b"));
    // 10 = 1010, 5 = 0101, OR = 1111 = 15
    ctx.push_obligation(ProofObligation::assert("is_15", "result == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "OR: 10 | 5 = 15");
}

#[test]
fn xor_operation() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 12"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == a ^ b"));
    // 12 = 1100, 10 = 1010, XOR = 0110 = 6
    ctx.push_obligation(ProofObligation::assert("is_6", "result == 6"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "XOR: 12 ^ 10 = 6");
}

#[test]
fn shift_left_operation() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "shift", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 3"));
    ctx.push_obligation(ProofObligation::assume("s", "shift == 4"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == val << shift"));
    // 3 << 4 = 48
    ctx.push_obligation(ProofObligation::assert("is_48", "result == 48"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SLL: 3 << 4 = 48");
}

#[test]
fn shift_right_logical() {
    let mut ctx = VerificationContext::new();
    for v in &["val", "shift", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 128"));
    ctx.push_obligation(ProofObligation::assume("s", "shift == 3"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == val >> shift"));
    // 128 >> 3 = 16
    ctx.push_obligation(ProofObligation::assert("is_16", "result == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SRL: 128 >> 3 = 16");
}

#[test]
fn set_less_than() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("slt", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 5"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "slt_def",
        "slt == if a < b { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1", "slt == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SLT: 5 < 10 → 1");
}

#[test]
fn multiply_operation() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 7"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 6"));
    ctx.push_obligation(ProofObligation::assume("r_def", "result == a * b"));
    ctx.push_obligation(ProofObligation::assert("is_42", "result == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "MUL: 7 * 6 = 42");
}

#[test]
fn not_operation() {
    // Bitwise NOT via XOR with all-ones
    let mut ctx = VerificationContext::new();
    for v in &["val", "mask", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 0"));
    ctx.push_obligation(ProofObligation::assume("m", "mask == 4294967295")); // 0xFFFFFFFF
    ctx.push_obligation(ProofObligation::assume("r_def", "result == val ^ mask"));
    ctx.push_obligation(ProofObligation::assert("is_max", "result == 4294967295"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "NOT: ~0 = 0xFFFFFFFF");
}
