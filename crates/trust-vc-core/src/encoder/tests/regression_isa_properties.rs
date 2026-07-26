// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn opcode_field_extraction() {
    let mut ctx = VerificationContext::new();
    for v in &["instruction", "opcode"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Opcode in bits [31:26] → instruction >> 26
    ctx.push_obligation(ProofObligation::assume(
        "instr",
        "instruction == 2285895680",
    )); // 0x88400000
    ctx.push_obligation(ProofObligation::assume(
        "op_def",
        "opcode == instruction >> 26",
    ));
    ctx.push_obligation(ProofObligation::assert("is_34", "opcode == 34")); // 0x88400000 >> 26 = 34
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ISA: extract opcode 34 from instruction");
}

#[test]
fn register_file_size() {
    let mut ctx = VerificationContext::new();
    for v in &["num_registers", "register_width_bits", "total_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 32 registers × 64 bits = 2048 bits = 256 bytes
    ctx.push_obligation(ProofObligation::assume("nr", "num_registers == 32"));
    ctx.push_obligation(ProofObligation::assume("rw", "register_width_bits == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bits == num_registers * register_width_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2048", "total_bits == 2048"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ISA: 32×64=2048 register bits");
}

#[test]
fn immediate_sign_extension() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imm12", i32_ty()); // 12-bit immediate
    ctx.declare_var_typed("extended", i32_ty()); // sign-extended to 32 bits
                                                 // A 12-bit value -5 sign-extended remains -5 in 32 bits
    ctx.push_obligation(ProofObligation::assume("i12", "imm12 == 0 - 5"));
    ctx.push_obligation(ProofObligation::assume("ext_def", "extended == imm12")); // sign extension is identity for i32
    ctx.push_obligation(ProofObligation::assert("is_neg5", "extended == 0 - 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ISA: sign-extend -5 stays -5");
}

#[test]
fn pc_relative_branch() {
    let mut ctx = VerificationContext::new();
    for v in &["pc", "offset", "target"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "pc == 4096"));
    ctx.push_obligation(ProofObligation::assume("o", "offset == 256"));
    ctx.push_obligation(ProofObligation::assume("t_def", "target == pc + offset"));
    ctx.push_obligation(ProofObligation::assert("is_4352", "target == 4352"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ISA: branch target 4096+256=4352");
}

#[test]
fn instruction_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "alignment"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // 4-byte instruction alignment
    ctx.push_obligation(ProofObligation::assume("addr", "address == 4096"));
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "a_def",
        "aligned == if address % alignment == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ISA: 4096 aligned to 4 bytes");
}

#[test]
fn instruction_encoding_width() {
    let mut ctx = VerificationContext::new();
    for v in &["encoding_bits", "encoding_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("eb", "encoding_bits == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "eby_def",
        "encoding_bytes == encoding_bits / 8",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "encoding_bytes == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ISA: 32-bit encoding = 4 bytes");
}

#[test]
fn condition_code_flags() {
    let mut ctx = VerificationContext::new();
    for v in &["result", "zero_flag", "negative_flag"] {
        ctx.declare_var_typed(v, i32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "result == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "zf_def",
        "zero_flag == if result == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "nf_def",
        "negative_flag == if result < 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("z_set", "zero_flag == 1"));
    ctx.push_obligation(ProofObligation::assert("n_clear", "negative_flag == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ISA: result=0 → Z=1, N=0");
}

#[test]
fn addressing_mode_base_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["base_reg", "offset", "effective_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("br", "base_reg == 65536")); // 0x10000
    ctx.push_obligation(ProofObligation::assume("off", "offset == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "effective_addr == base_reg + offset",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_65664",
        "effective_addr == 65664",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ISA: base+offset = 65536+128 = 65664");
}

#[test]
fn interrupt_vector_table() {
    let mut ctx = VerificationContext::new();
    for v in &["vector_num", "entry_size", "table_base", "handler_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("vn", "vector_num == 14")); // page fault
    ctx.push_obligation(ProofObligation::assume("es", "entry_size == 8"));
    ctx.push_obligation(ProofObligation::assume("tb", "table_base == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ha_def",
        "handler_addr == table_base + vector_num * entry_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_112", "handler_addr == 112")); // 14 * 8
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "IVT: vector 14 × 8 = offset 112");
}

#[test]
fn stack_frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "locals_bytes",
        "saved_regs",
        "reg_size",
        "saved_bytes",
        "frame_size",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("lb", "locals_bytes == 48"));
    ctx.push_obligation(ProofObligation::assume("sr", "saved_regs == 6"));
    ctx.push_obligation(ProofObligation::assume("rs", "reg_size == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "sb_def",
        "saved_bytes == saved_regs * reg_size",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "fs_def",
        "frame_size == locals_bytes + saved_bytes",
    ));
    ctx.push_obligation(ProofObligation::assert("sb_48", "saved_bytes == 48"));
    ctx.push_obligation(ProofObligation::assert("fs_96", "frame_size == 96"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "stack frame: 48 locals + 6×8 saved = 96");
}
