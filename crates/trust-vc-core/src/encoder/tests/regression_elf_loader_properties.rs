// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn elf_magic_number() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("magic_byte0", u32_ty());
    ctx.declare_var_typed("magic_byte1", u32_ty());
    ctx.declare_var_typed("magic_byte2", u32_ty());
    ctx.declare_var_typed("magic_byte3", u32_ty());
    ctx.declare_var_typed("valid_elf", i32_ty());
    // ELF magic: 0x7F 'E' 'L' 'F'
    ctx.push_obligation(ProofObligation::assume("m0", "magic_byte0 == 127")); // 0x7F
    ctx.push_obligation(ProofObligation::assume("m1", "magic_byte1 == 69")); // 'E'
    ctx.push_obligation(ProofObligation::assume("m2", "magic_byte2 == 76")); // 'L'
    ctx.push_obligation(ProofObligation::assume("m3", "magic_byte3 == 70")); // 'F'
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_elf == if magic_byte0 == 127 && magic_byte1 == 69 && magic_byte2 == 76 && magic_byte3 == 70 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_elf == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ELF: 7F 45 4C 46 magic → valid");
}

#[test]
fn program_header_entry_size() {
    let mut ctx = VerificationContext::new();
    for v in &["phentsize", "phnum", "total_ph_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // ELF32: program header entry = 32 bytes
    ctx.push_obligation(ProofObligation::assume("pe", "phentsize == 32"));
    ctx.push_obligation(ProofObligation::assume("pn", "phnum == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "tpb_def",
        "total_ph_bytes == phentsize * phnum",
    ));
    ctx.push_obligation(ProofObligation::assert("is_128", "total_ph_bytes == 128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ELF: 32 × 4 = 128 bytes for program headers");
}

#[test]
fn load_segment_bounds() {
    let mut ctx = VerificationContext::new();
    for v in &["vaddr", "memsz", "end_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_ram", i32_ty());
    // PT_LOAD segment must fit in RAM
    ctx.push_obligation(ProofObligation::assume("va", "vaddr == 536870912")); // 0x20000000
    ctx.push_obligation(ProofObligation::assume("ms", "memsz == 32768")); // 32KB
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "end_addr == vaddr + memsz",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_ram == if vaddr >= 536870912 && end_addr <= 537001984 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_correct_end",
        "end_addr == 536903680",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_ram == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ELF: segment 0x20000000+32KB fits in 128KB RAM");
}

#[test]
fn bss_zero_fill_size() {
    let mut ctx = VerificationContext::new();
    for v in &["memsz", "filesz", "zero_fill_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // .bss: memsz > filesz; difference is zero-filled
    ctx.push_obligation(ProofObligation::assume("ms", "memsz == 8192"));
    ctx.push_obligation(ProofObligation::assume("fs", "filesz == 0")); // pure BSS
    ctx.push_obligation(ProofObligation::assume(
        "zf_def",
        "zero_fill_bytes == memsz - filesz",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_8192",
        "zero_fill_bytes == 8192",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ELF .bss: 8192 - 0 = 8192 bytes to zero");
}

#[test]
fn entry_point_in_text() {
    let mut ctx = VerificationContext::new();
    for v in &["entry_point", "text_start", "text_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_entry", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ep", "entry_point == 134217984")); // 0x08000100
    ctx.push_obligation(ProofObligation::assume("ts", "text_start == 134217728")); // 0x08000000
    ctx.push_obligation(ProofObligation::assume("tsz", "text_size == 65536")); // 64KB
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_entry == if entry_point >= text_start && entry_point < text_start + text_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_entry == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ELF: entry 0x08000100 in .text [0x08000000, +64KB)",
    );
}

#[test]
fn section_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["section_addr", "alignment"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sa", "section_addr == 536870912")); // 0x20000000
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 4")); // word-aligned
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "aligned == if section_addr % alignment == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ELF: 0x20000000 word-aligned");
}

#[test]
fn relocation_addend() {
    let mut ctx = VerificationContext::new();
    for v in &["symbol_addr", "addend", "relocated_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // R_ARM_ABS32: S + A (symbol + addend)
    ctx.push_obligation(ProofObligation::assume("sa", "symbol_addr == 134218000")); // symbol location
    ctx.push_obligation(ProofObligation::assume("a", "addend == 16")); // offset into struct
    ctx.push_obligation(ProofObligation::assume(
        "ra_def",
        "relocated_addr == symbol_addr + addend",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_correct",
        "relocated_addr == 134218016",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ELF reloc: 134218000 + 16 = 134218016");
}

#[test]
fn segment_overlap_check() {
    let mut ctx = VerificationContext::new();
    for v in &["seg1_start", "seg1_end", "seg2_start", "seg2_end"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("overlaps", i32_ty());
    // Two load segments must not overlap in memory
    ctx.push_obligation(ProofObligation::assume("s1s", "seg1_start == 536870912")); // 0x20000000
    ctx.push_obligation(ProofObligation::assume("s1e", "seg1_end == 536879104")); // + 8KB
    ctx.push_obligation(ProofObligation::assume("s2s", "seg2_start == 536879104")); // starts after seg1
    ctx.push_obligation(ProofObligation::assume("s2e", "seg2_end == 536887296")); // + 8KB
    ctx.push_obligation(ProofObligation::assume(
        "ov_def",
        "overlaps == if seg1_end > seg2_start && seg2_end > seg1_start { 1 } else { 0 }",
    ));
    // seg1_end == seg2_start → NO overlap (end is exclusive)
    ctx.push_obligation(ProofObligation::assert("no_overlap", "overlaps == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ELF: adjacent segments [+8KB][+8KB] don't overlap");
}

#[test]
fn string_table_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["strtab_offset", "name_offset", "absolute_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_strtab", i32_ty());
    ctx.push_obligation(ProofObligation::assume("so", "strtab_offset == 4096"));
    ctx.push_obligation(ProofObligation::assume("no", "name_offset == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "absolute_offset == strtab_offset + name_offset",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_4138",
        "absolute_offset == 4138",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ELF strtab: 4096 + 42 = 4138");
}

#[test]
fn dynamic_segment_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_segments", "load_segments", "dynamic_segments"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("has_dynamic", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ts", "total_segments == 6"));
    ctx.push_obligation(ProofObligation::assume("ls", "load_segments == 4"));
    ctx.push_obligation(ProofObligation::assume("ds", "dynamic_segments == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "hd_def",
        "has_dynamic == if dynamic_segments > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "has_dynamic == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "accounted",
        "load_segments + dynamic_segments <= total_segments",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ELF: 4 LOAD + 1 DYNAMIC <= 6 total segments");
}
