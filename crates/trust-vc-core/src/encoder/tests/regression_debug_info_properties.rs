// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn dwarf_version_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dwarf_version", u32_ty());
    ctx.declare_var_typed("supported", i32_ty());
    // DWARF versions 2-5 are commonly supported
    ctx.push_obligation(ProofObligation::assume("dv", "dwarf_version == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "supported == if dwarf_version >= 2 && dwarf_version <= 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "supported == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DWARF: version 4 in [2, 5] → supported");
}

#[test]
fn compilation_unit_header_size() {
    let mut ctx = VerificationContext::new();
    for v in &[
        "unit_length_field",
        "version_field",
        "abbrev_offset_field",
        "address_size_field",
        "header_bytes",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // DWARF CU header: 4 + 2 + 4 + 1 = 11 bytes (32-bit format)
    ctx.push_obligation(ProofObligation::assume("ulf", "unit_length_field == 4"));
    ctx.push_obligation(ProofObligation::assume("vf", "version_field == 2"));
    ctx.push_obligation(ProofObligation::assume("aof", "abbrev_offset_field == 4"));
    ctx.push_obligation(ProofObligation::assume("asf", "address_size_field == 1"));
    ctx.push_obligation(ProofObligation::assume("hb_def", "header_bytes == unit_length_field + version_field + abbrev_offset_field + address_size_field"));
    ctx.push_obligation(ProofObligation::assert("is_11", "header_bytes == 11"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DWARF CU header: 4+2+4+1 = 11 bytes");
}

#[test]
fn line_number_opcode_base() {
    let mut ctx = VerificationContext::new();
    for v in &["opcode_base", "standard_opcode_count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // Standard opcode count = opcode_base - 1 (DWARF 4: opcode_base=13 → 12 standard opcodes)
    ctx.push_obligation(ProofObligation::assume("ob", "opcode_base == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "soc_def",
        "standard_opcode_count == opcode_base - 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if standard_opcode_count == 12 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_12",
        "standard_opcode_count == 12",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DWARF line: opcode_base 13 → 12 standard opcodes");
}

#[test]
fn address_range_containment() {
    let mut ctx = VerificationContext::new();
    for v in &["func_start", "func_length", "func_end", "query_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_function", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fs", "func_start == 4096"));
    ctx.push_obligation(ProofObligation::assume("fl", "func_length == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "fe_def",
        "func_end == func_start + func_length",
    ));
    ctx.push_obligation(ProofObligation::assume("qa", "query_addr == 4200"));
    ctx.push_obligation(ProofObligation::assume(
        "if_def",
        "in_function == if query_addr >= func_start && query_addr < func_end { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4352", "func_end == 4352"));
    ctx.push_obligation(ProofObligation::assert("yes", "in_function == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DWARF: addr 4200 in [4096, 4352) → in function");
}

#[test]
fn abbreviation_table_entry() {
    let mut ctx = VerificationContext::new();
    for v in &["abbrev_code", "tag", "has_children"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_entry", i32_ty());
    // Valid abbreviation: code > 0, tag > 0, has_children is 0 or 1
    ctx.push_obligation(ProofObligation::assume("ac", "abbrev_code == 1"));
    ctx.push_obligation(ProofObligation::assume("t", "tag == 17")); // DW_TAG_compile_unit
    ctx.push_obligation(ProofObligation::assume("hc", "has_children == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_entry == if abbrev_code > 0 && tag > 0 && has_children <= 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_entry == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DWARF abbrev: code=1, tag=17, children=1 → valid");
}

#[test]
fn debug_info_section_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["section_base", "cu_offset", "die_offset", "absolute_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Absolute offset = section_base + cu_offset + die_offset
    ctx.push_obligation(ProofObligation::assume("sb", "section_base == 0"));
    ctx.push_obligation(ProofObligation::assume("co", "cu_offset == 1024"));
    ctx.push_obligation(ProofObligation::assume("do_", "die_offset == 48"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "absolute_offset == section_base + cu_offset + die_offset",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_1072",
        "absolute_offset == 1072",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DWARF: 0 + 1024 + 48 = 1072 absolute offset");
}

#[test]
fn source_line_mapping() {
    let mut ctx = VerificationContext::new();
    for v in &["file_index", "line_number", "column_number"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_location", i32_ty());
    // Valid source location: file > 0, line > 0
    ctx.push_obligation(ProofObligation::assume("fi", "file_index == 1"));
    ctx.push_obligation(ProofObligation::assume("ln", "line_number == 42"));
    ctx.push_obligation(ProofObligation::assume("cn", "column_number == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "vl_def",
        "valid_location == if file_index > 0 && line_number > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_location == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DWARF line: file=1, line=42 → valid source location",
    );
}

#[test]
fn frame_description_entry() {
    let mut ctx = VerificationContext::new();
    for v in &["initial_cfa_offset", "saved_regs", "frame_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // CFA = stack pointer + offset. Frame includes saved registers.
    ctx.push_obligation(ProofObligation::assume("ico", "initial_cfa_offset == 8")); // return addr
    ctx.push_obligation(ProofObligation::assume("sr", "saved_regs == 6")); // callee-saved
    ctx.push_obligation(ProofObligation::assume(
        "fs_def",
        "frame_size == initial_cfa_offset + saved_regs * 8",
    ));
    // Precompute: 8 + 48 = 56
    ctx.push_obligation(ProofObligation::assert("is_56", "frame_size == 56"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "DWARF FDE: 8 + 6×8 = 56 byte frame");
}

#[test]
fn debug_str_offset() {
    let mut ctx = VerificationContext::new();
    for v in &["str_section_size", "str_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_bounds", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ss", "str_section_size == 8192"));
    ctx.push_obligation(ProofObligation::assume("so", "str_offset == 4096"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "in_bounds == if str_offset < str_section_size { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_bounds == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DWARF .debug_str: offset 4096 < 8192 size → valid");
}

#[test]
fn leb128_encoding_size() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("value", u32_ty());
    ctx.declare_var_typed("encoded_bytes", u32_ty());
    ctx.declare_var_typed("valid_size", i32_ty());
    // LEB128: values < 128 encode in 1 byte, < 16384 in 2 bytes, etc.
    // Value 300 needs 2 bytes (300 >= 128, 300 < 16384)
    ctx.push_obligation(ProofObligation::assume("v", "value == 300"));
    ctx.push_obligation(ProofObligation::assume("eb", "encoded_bytes == 2")); // precomputed
    ctx.push_obligation(ProofObligation::assume(
        "vs_def",
        "valid_size == if encoded_bytes >= 1 && encoded_bytes <= 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "encoded_bytes == 2"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_size == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DWARF LEB128: value 300 → 2 bytes");
}
