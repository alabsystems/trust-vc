// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn read_after_write_returns_written_value() {
    let mut ctx = VerificationContext::new();
    for v in &["written", "read_back"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("w", "written == 42"));
    ctx.push_obligation(ProofObligation::assume("r_def", "read_back == written"));
    ctx.push_obligation(ProofObligation::assert("same", "read_back == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "read after write returns 42");
}

#[test]
fn zero_register_always_zero() {
    // x0 in RISC-V is always 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x0", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x0_val", "x0 == 0"));
    ctx.push_obligation(ProofObligation::assert("always_zero", "x0 == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x0 is always 0");
}

#[test]
fn write_to_zero_register_ignored() {
    let mut ctx = VerificationContext::new();
    for v in &["reg_idx", "write_val", "x0_after"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ri", "reg_idx == 0"));
    ctx.push_obligation(ProofObligation::assume("wv", "write_val == 99"));
    ctx.push_obligation(ProofObligation::assume(
        "x0a_def",
        "x0_after == if reg_idx == 0 { 0 } else { write_val }",
    ));
    ctx.push_obligation(ProofObligation::assert("still_zero", "x0_after == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "write to x0 ignored → still 0");
}

#[test]
fn register_index_in_range() {
    // 32 registers: index must be < 32
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reg_idx", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ri", "reg_idx == 31"));
    ctx.push_obligation(ProofObligation::assert("in_range", "reg_idx < 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "register index 31 < 32");
}

#[test]
fn two_reads_same_register_identical() {
    let mut ctx = VerificationContext::new();
    for v in &["read1", "read2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r1", "read1 == 100"));
    ctx.push_obligation(ProofObligation::assume("r2_def", "read2 == read1"));
    ctx.push_obligation(ProofObligation::assert("identical", "read1 == read2"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two reads of same register identical");
}

#[test]
fn program_counter_increment() {
    let mut ctx = VerificationContext::new();
    for v in &["pc", "new_pc"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "pc == 1000"));
    ctx.push_obligation(ProofObligation::assume("np_def", "new_pc == pc + 4"));
    ctx.push_obligation(ProofObligation::assert("is_1004", "new_pc == 1004"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "PC: 1000 + 4 = 1004");
}

#[test]
fn stack_pointer_decrement() {
    // Push: SP decreases by frame size
    let mut ctx = VerificationContext::new();
    for v in &["sp", "frame_size", "new_sp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "sp == 4096"));
    ctx.push_obligation(ProofObligation::assume("fs", "frame_size == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "nsp_def",
        "new_sp == sp - frame_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4080", "new_sp == 4080"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SP: 4096 - 16 = 4080");
}

#[test]
fn link_register_save_return_address() {
    let mut ctx = VerificationContext::new();
    for v in &["pc", "lr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "pc == 2000"));
    ctx.push_obligation(ProofObligation::assume("lr_def", "lr == pc + 4"));
    ctx.push_obligation(ProofObligation::assert("return_addr", "lr == 2004"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LR saves return address: 2004");
}

#[test]
fn condition_flags_zero_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("result", i32_ty());
    ctx.declare_var_typed("zero_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "result == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "zf_def",
        "zero_flag == if result == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("zf_set", "zero_flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "result=0 → zero flag set");
}

#[test]
fn register_bank_select() {
    // High bank: registers 16-31, low bank: 0-15
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reg_idx", u32_ty());
    ctx.declare_var_typed("is_high_bank", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ri", "reg_idx == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ihb_def",
        "is_high_bank == if reg_idx >= 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("high", "is_high_bank == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "register 20 in high bank");
}
