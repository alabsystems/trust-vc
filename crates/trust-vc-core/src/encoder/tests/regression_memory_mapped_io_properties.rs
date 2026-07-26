// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn register_read_after_write() {
    let mut ctx = VerificationContext::new();
    for v in &["written_value", "read_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("wv", "written_value == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "rv_def",
        "read_value == written_value",
    ));
    ctx.push_obligation(ProofObligation::assert("same", "read_value == 42"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MMIO: write 42, read 42");
}

#[test]
fn register_offset_calculation() {
    let mut ctx = VerificationContext::new();
    for v in &["base_addr", "reg_index", "reg_size", "effective_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ba", "base_addr == 4096"));
    ctx.push_obligation(ProofObligation::assume("ri", "reg_index == 3"));
    ctx.push_obligation(ProofObligation::assume("rs", "reg_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "effective_addr == base_addr + reg_index * reg_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4108", "effective_addr == 4108"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "MMIO offset: 4096 + 3*4 = 4108");
}

#[test]
fn bit_field_extraction() {
    let mut ctx = VerificationContext::new();
    for v in &["register_val", "mask", "shift", "field_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("rv", "register_val == 255")); // 0xFF
    ctx.push_obligation(ProofObligation::assume("m", "mask == 15")); // 0x0F
    ctx.push_obligation(ProofObligation::assume(
        "fv_def",
        "field_val == register_val & mask",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "field_val == 15"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bitfield: 0xFF & 0x0F = 0x0F");
}

#[test]
fn status_register_flags() {
    let mut ctx = VerificationContext::new();
    for v in &["status_reg", "busy_bit", "error_bit"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("sr", "status_reg == 5")); // bits 0 and 2 set
    ctx.push_obligation(ProofObligation::assume(
        "bb_def",
        "busy_bit == status_reg & 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "eb_def",
        "error_bit == status_reg & 4",
    ));
    ctx.push_obligation(ProofObligation::assert("busy_set", "busy_bit == 1"));
    ctx.push_obligation(ProofObligation::assert("error_set", "error_bit == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "status: reg=5, busy=1, error=4");
}

#[test]
fn write_mask_preserves_bits() {
    let mut ctx = VerificationContext::new();
    for v in &["old_val", "write_val", "write_mask", "new_val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ov", "old_val == 240")); // 0xF0
    ctx.push_obligation(ProofObligation::assume("wv", "write_val == 10")); // 0x0A
    ctx.push_obligation(ProofObligation::assume("wm", "write_mask == 15")); // 0x0F — only low nibble writable
                                                                            // new = (old & ~mask) | (write & mask)
                                                                            // Simplified: since old=0xF0 and mask=0x0F, old & ~mask = 0xF0, write & mask = 0x0A
                                                                            // new = 0xF0 | 0x0A = 0xFA = 250
    ctx.push_obligation(ProofObligation::assume(
        "nv_def",
        "new_val == (old_val & (4294967295 - write_mask)) | (write_val & write_mask)",
    ));
    ctx.push_obligation(ProofObligation::assert("is_250", "new_val == 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "write mask: preserve high nibble, write low");
}

#[test]
fn dma_transfer_size() {
    let mut ctx = VerificationContext::new();
    for v in &["block_count", "block_size", "total_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("bc", "block_count == 16"));
    ctx.push_obligation(ProofObligation::assume("bs", "block_size == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bytes == block_count * block_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8192", "total_bytes == 8192"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DMA: 16 × 512 = 8192 bytes");
}

#[test]
fn interrupt_pending_count() {
    let mut ctx = VerificationContext::new();
    for v in &["irq_status", "handled", "pending"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("is", "irq_status == 7")); // 3 IRQs pending
    ctx.push_obligation(ProofObligation::assume("h", "handled == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "pending == irq_status - handled",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "pending == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "IRQ: 7 total - 2 handled = 5 pending");
}

#[test]
fn memory_region_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["region_start", "region_size", "region_end", "access_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_bounds", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rs", "region_start == 8192"));
    ctx.push_obligation(ProofObligation::assume("rsz", "region_size == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "re_def",
        "region_end == region_start + region_size",
    ));
    ctx.push_obligation(ProofObligation::assume("aa", "access_addr == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_bounds == if access_addr >= region_start && access_addr < region_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("valid", "in_bounds == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MMIO region: 10000 in [8192, 12288)");
}

#[test]
fn fifo_buffer_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["writes", "reads", "depth", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overflow", i32_ty());
    ctx.push_obligation(ProofObligation::assume("w", "writes == 50"));
    ctx.push_obligation(ProofObligation::assume("r", "reads == 35"));
    ctx.push_obligation(ProofObligation::assume("d_def", "depth == writes - reads"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "of_def",
        "overflow == if depth > max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_15", "depth == 15"));
    ctx.push_obligation(ProofObligation::assert("no_overflow", "overflow == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "FIFO: 50-35=15 depth, no overflow (max 64)");
}

#[test]
fn bus_address_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "alignment", "remainder"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    ctx.push_obligation(ProofObligation::assume("a", "address == 4096"));
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "rem_def",
        "remainder == address % alignment",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "aligned_def",
        "aligned == if remainder == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_aligned", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "bus: 4096 % 16 == 0 → aligned");
}
