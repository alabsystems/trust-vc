// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn flash_region_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["flash_origin", "flash_length", "flash_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // MEMORY { FLASH : ORIGIN = 0x08000000, LENGTH = 512K }
    ctx.push_obligation(ProofObligation::assume("fo", "flash_origin == 134217728")); // 0x08000000
    ctx.push_obligation(ProofObligation::assume("fl", "flash_length == 524288")); // 512KB
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "flash_end == flash_origin + flash_length",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_correct",
        "flash_end == 134742016",
    )); // 0x08080000
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: FLASH [0x08000000, 0x08080000)");
}

#[test]
fn ram_region_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["ram_origin", "ram_length", "ram_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ro", "ram_origin == 536870912")); // 0x20000000
    ctx.push_obligation(ProofObligation::assume("rl", "ram_length == 131072")); // 128KB
    ctx.push_obligation(ProofObligation::assume(
        "re_def",
        "ram_end == ram_origin + ram_length",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_correct",
        "ram_end == 537001984",
    )); // 0x20020000
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: RAM [0x20000000, 0x20020000)");
}

#[test]
fn section_placement_order() {
    let mut ctx = VerificationContext::new();
    for v in &["text_end", "rodata_start", "data_start"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ordered", i32_ty());
    // Sections must be ordered: .text < .rodata < .data in flash
    ctx.push_obligation(ProofObligation::assume("te", "text_end == 134230016")); // .text ends
    ctx.push_obligation(ProofObligation::assume("rs", "rodata_start == 134230016")); // .rodata starts
    ctx.push_obligation(ProofObligation::assume("ds", "data_start == 134234112")); // .data starts
    ctx.push_obligation(ProofObligation::assume(
        "o_def",
        "ordered == if text_end <= rodata_start && rodata_start <= data_start { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "ordered == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: .text <= .rodata <= .data ordering");
}

#[test]
fn stack_size_allocation() {
    let mut ctx = VerificationContext::new();
    for v in &["ram_end", "stack_size", "stack_top", "stack_bottom"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Stack at end of RAM, growing downward
    ctx.push_obligation(ProofObligation::assume("re", "ram_end == 537001984")); // 0x20020000
    ctx.push_obligation(ProofObligation::assume("ss", "stack_size == 8192")); // 8KB
    ctx.push_obligation(ProofObligation::assume("st_def", "stack_top == ram_end"));
    ctx.push_obligation(ProofObligation::assume(
        "sb_def",
        "stack_bottom == stack_top - stack_size",
    ));
    ctx.push_obligation(ProofObligation::assert("top", "stack_top == 537001984"));
    ctx.push_obligation(ProofObligation::assert(
        "bottom",
        "stack_bottom == 536993792",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: stack [0x2001E000, 0x20020000) 8KB");
}

#[test]
fn heap_between_bss_and_stack() {
    let mut ctx = VerificationContext::new();
    for v in &["bss_end", "stack_bottom", "heap_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("heap_fits", i32_ty());
    ctx.push_obligation(ProofObligation::assume("be", "bss_end == 536879104")); // after .bss
    ctx.push_obligation(ProofObligation::assume("sb", "stack_bottom == 536993792")); // before stack
    ctx.push_obligation(ProofObligation::assume(
        "hs_def",
        "heap_size == stack_bottom - bss_end",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "hf_def",
        "heap_fits == if heap_size > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_114688", "heap_size == 114688")); // 112KB
    ctx.push_obligation(ProofObligation::assert("ok", "heap_fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: heap 112KB between .bss and stack");
}

#[test]
fn data_lma_vma_mapping() {
    let mut ctx = VerificationContext::new();
    for v in &["data_lma", "data_vma", "data_size", "copy_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // .data: loaded from flash (LMA) → copied to RAM (VMA) at startup
    ctx.push_obligation(ProofObligation::assume("dlma", "data_lma == 134234112")); // in flash
    ctx.push_obligation(ProofObligation::assume("dvma", "data_vma == 536870912")); // in RAM
    ctx.push_obligation(ProofObligation::assume("ds", "data_size == 4096"));
    ctx.push_obligation(ProofObligation::assume("cb_def", "copy_bytes == data_size"));
    ctx.push_obligation(ProofObligation::assert(
        "different_regions",
        "data_lma != data_vma",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4096", "copy_bytes == 4096"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: .data LMA(flash) → VMA(RAM), 4KB copy");
}

#[test]
fn vector_table_at_origin() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vectors_addr", u32_ty());
    ctx.declare_var_typed("flash_origin", u32_ty());
    ctx.declare_var_typed("at_origin", i32_ty());
    // Vector table must be at flash origin (first thing in flash)
    ctx.push_obligation(ProofObligation::assume("va", "vectors_addr == 134217728")); // 0x08000000
    ctx.push_obligation(ProofObligation::assume("fo", "flash_origin == 134217728"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "at_origin == if vectors_addr == flash_origin { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "at_origin == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: vectors at flash origin 0x08000000");
}

#[test]
fn total_flash_usage() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "text_size",
        "rodata_size",
        "data_size",
        "total_flash_used",
        "flash_length",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits_in_flash", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ts", "text_size == 32768")); // 32KB
    ctx.push_obligation(ProofObligation::assume("rs", "rodata_size == 8192")); // 8KB
    ctx.push_obligation(ProofObligation::assume("ds", "data_size == 4096")); // 4KB
    ctx.push_obligation(ProofObligation::assume(
        "tfu_def",
        "total_flash_used == text_size + rodata_size + data_size",
    ));
    ctx.push_obligation(ProofObligation::assume("fl", "flash_length == 524288")); // 512KB
    ctx.push_obligation(ProofObligation::assume(
        "fif_def",
        "fits_in_flash == if total_flash_used <= flash_length { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_45056",
        "total_flash_used == 45056",
    )); // 44KB
    ctx.push_obligation(ProofObligation::assert("ok", "fits_in_flash == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: 32K+8K+4K = 44KB << 512KB flash");
}

#[test]
fn alignment_padding() {
    let mut ctx = VerificationContext::new();
    for v in &["section_end", "alignment", "padding"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("next_section_start", u32_ty());
    // ALIGN(4) inserts padding to reach next 4-byte boundary
    // section_end=1023 → next aligned = 1024, padding = 1
    ctx.push_obligation(ProofObligation::assume("se", "section_end == 1023"));
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 4"));
    // Precompute: 1023 mod 4 = 3, padding = 4-3 = 1
    ctx.push_obligation(ProofObligation::assume("p", "padding == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "next_section_start == section_end + padding",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1024",
        "next_section_start == 1024",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "linker: ALIGN(4) 1023 + 1 = 1024");
}

#[test]
fn ccm_ram_region() {
    let mut ctx = VerificationContext::new();
    for v in &["ccm_origin", "ccm_length", "ccm_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("separate_from_main_ram", i32_ty());
    // CCM (Core Coupled Memory): separate from main SRAM
    ctx.push_obligation(ProofObligation::assume("co", "ccm_origin == 268435456")); // 0x10000000
    ctx.push_obligation(ProofObligation::assume("cl", "ccm_length == 65536")); // 64KB
    ctx.push_obligation(ProofObligation::assume(
        "ce_def",
        "ccm_end == ccm_origin + ccm_length",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sfmr_def",
        "separate_from_main_ram == if ccm_end < 536870912 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("end", "ccm_end == 268500992")); // 0x10010000
    ctx.push_obligation(ProofObligation::assert(
        "separate",
        "separate_from_main_ram == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "linker: CCM [0x10000000, 0x10010000) separate from SRAM",
    );
}
