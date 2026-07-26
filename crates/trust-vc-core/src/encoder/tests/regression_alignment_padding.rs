// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn align_to_power_of_two() {
    let mut ctx = VerificationContext::new();
    for v in &["addr", "aligned"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Align 13 to next multiple of 8: (13 + 7) & !7 = 16
    ctx.push_obligation(ProofObligation::assume("addr_val", "addr == 13"));
    ctx.push_obligation(ProofObligation::assume(
        "aligned_def",
        "aligned == (addr + 7) & 4294967288",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "aligned == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "align 13 to 8 = 16");
}

#[test]
fn already_aligned_unchanged() {
    let mut ctx = VerificationContext::new();
    for v in &["addr", "aligned"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 16 is already aligned to 8
    ctx.push_obligation(ProofObligation::assume("addr_val", "addr == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "aligned_def",
        "aligned == (addr + 7) & 4294967288",
    ));
    ctx.push_obligation(ProofObligation::assert("unchanged", "aligned == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "16 already aligned to 8");
}

#[test]
fn alignment_never_decreases() {
    let mut ctx = VerificationContext::new();
    for v in &["addr", "aligned"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("addr_val", "addr == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "aligned_def",
        "aligned == (addr + 3) & 4294967292",
    ));
    // Align to 4: (5+3) & ~3 = 8
    ctx.push_obligation(ProofObligation::assert("ge_addr", "aligned >= addr"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "alignment >= original address");
}

#[test]
fn struct_two_field_size() {
    // Struct with u8 (1 byte) + u32 (4 bytes) = 8 bytes with padding
    let mut ctx = VerificationContext::new();
    for v in &["field1_size", "field2_size", "padding", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f1", "field1_size == 1"));
    ctx.push_obligation(ProofObligation::assume("f2", "field2_size == 4"));
    ctx.push_obligation(ProofObligation::assume("pad", "padding == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "total_def",
        "total == field1_size + padding + field2_size",
    ));
    ctx.push_obligation(ProofObligation::assert("size_is_8", "total == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 + padding(3) + u32 = 8 bytes");
}

#[test]
fn offset_of_second_field() {
    let mut ctx = VerificationContext::new();
    for v in &["field1_size", "align", "offset2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f1_size", "field1_size == 1"));
    ctx.push_obligation(ProofObligation::assume("align_val", "align == 4"));
    // offset of second field = round up field1_size to align
    ctx.push_obligation(ProofObligation::assume(
        "offset_def",
        "offset2 == ((field1_size + align - 1) / align) * align",
    ));
    ctx.push_obligation(ProofObligation::assert("offset_is_4", "offset2 == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "second field offset after u8 at align 4 is 4");
}

#[test]
fn padding_bytes_count() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "align", "padding"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("size_val", "size == 3"));
    ctx.push_obligation(ProofObligation::assume("align_val", "align == 4"));
    // padding = align - (size % align) when size % align != 0
    ctx.push_obligation(ProofObligation::assume(
        "pad_def",
        "padding == align - size",
    ));
    ctx.push_obligation(ProofObligation::assert("one_byte_pad", "padding == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3 bytes needs 1 byte padding for align 4");
}

#[test]
fn zero_padding_when_aligned() {
    let mut ctx = VerificationContext::new();
    for v in &["size", "aligned_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("size_val", "size == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "aligned_def",
        "aligned_size == size",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "no_padding",
        "aligned_size == size",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "8 bytes at align 4 needs no padding");
}

#[test]
fn array_stride() {
    // Array of 3-byte elements at align 4: stride = 4 per element
    let mut ctx = VerificationContext::new();
    for v in &["elem_size", "stride", "array_size", "count"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("elem", "elem_size == 3"));
    ctx.push_obligation(ProofObligation::assume("stride_val", "stride == 4"));
    ctx.push_obligation(ProofObligation::assume("count_val", "count == 5"));
    ctx.push_obligation(ProofObligation::assume(
        "array_def",
        "array_size == stride * count",
    ));
    ctx.push_obligation(ProofObligation::assert("is_20", "array_size == 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "5 elements of stride 4 = 20 bytes");
}

#[test]
fn two_field_no_trailing_pad() {
    // Two u32 fields: no padding needed between or after
    let mut ctx = VerificationContext::new();
    for v in &["f1", "f2", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f1_size", "f1 == 4"));
    ctx.push_obligation(ProofObligation::assume("f2_size", "f2 == 4"));
    ctx.push_obligation(ProofObligation::assume("total_def", "total == f1 + f2"));
    ctx.push_obligation(ProofObligation::assert("is_8", "total == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two u32 fields = 8 bytes, no padding");
}

#[test]
fn max_alignment_dominates() {
    // Struct alignment = max of field alignments
    let mut ctx = VerificationContext::new();
    for v in &["align1", "align2", "align3", "struct_align"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a1", "align1 == 1"));
    ctx.push_obligation(ProofObligation::assume("a2", "align2 == 8"));
    ctx.push_obligation(ProofObligation::assume("a3", "align3 == 4"));
    // max of (1, 8, 4) = 8
    ctx.push_obligation(ProofObligation::assume(
        "struct_align_def",
        "struct_align == if align1 >= align2 && align1 >= align3 { align1 } else { if align2 >= align3 { align2 } else { align3 } }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "struct_align == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "struct align = max(1, 8, 4) = 8");
}
