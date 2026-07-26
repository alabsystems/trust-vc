// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn struct_field_offset() {
    // First field at offset 0
    let mut ctx = VerificationContext::new();
    for v in &["base", "field_offset", "field_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b", "base == 1000"));
    ctx.push_obligation(ProofObligation::assume("fo", "field_offset == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "fa_def",
        "field_addr == base + field_offset",
    ));
    ctx.push_obligation(ProofObligation::assert("first_field", "field_addr == base"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "first field at offset 0 = base addr");
}

#[test]
fn alignment_padding() {
    // 4-byte aligned: addr must be multiple of 4
    let mut ctx = VerificationContext::new();
    for v in &["addr", "alignment", "remainder"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("a", "addr == 1024"));
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "remainder == addr % alignment",
    ));
    ctx.push_obligation(ProofObligation::assert("aligned", "remainder == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "1024 is 4-byte aligned");
}

#[test]
fn array_element_address() {
    // arr[i] = base + i * elem_size
    let mut ctx = VerificationContext::new();
    for v in &["base", "index", "elem_size", "elem_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("b", "base == 2000"));
    ctx.push_obligation(ProofObligation::assume("i", "index == 3"));
    ctx.push_obligation(ProofObligation::assume("es", "elem_size == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "ea_def",
        "elem_addr == base + index * elem_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2024", "elem_addr == 2024"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "arr[3] at base 2000, size 8 = 2024");
}

#[test]
fn size_of_pair() {
    // Pair of two u32s = 8 bytes
    let mut ctx = VerificationContext::new();
    for v in &["field1_size", "field2_size", "total_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("f1", "field1_size == 4"));
    ctx.push_obligation(ProofObligation::assume("f2", "field2_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_size == field1_size + field2_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "total_size == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "two u32 fields = 8 bytes");
}

#[test]
fn slice_fat_pointer() {
    // Slice = (ptr, len), 2 * pointer_size
    let mut ctx = VerificationContext::new();
    for v in &["ptr_size", "fat_ptr_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ps", "ptr_size == 8")); // 64-bit
    ctx.push_obligation(ProofObligation::assume(
        "fps_def",
        "fat_ptr_size == ptr_size + ptr_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_16", "fat_ptr_size == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fat pointer = 2 * 8 = 16 bytes");
}

#[test]
fn enum_discriminant_size() {
    // Enum with <= 256 variants needs 1 byte discriminant
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("variant_count", u32_ty());
    ctx.declare_var_typed("fits_in_byte", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vc", "variant_count == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "fib_def",
        "fits_in_byte == if variant_count <= 256 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("fits", "fits_in_byte == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "200 variants fits in 1 byte discriminant");
}

#[test]
fn option_niche_optimization() {
    // Option<NonZero<u32>> is same size as u32 (niche = 0)
    let mut ctx = VerificationContext::new();
    for v in &["inner_size", "option_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("is", "inner_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "os_def",
        "option_size == inner_size",
    )); // niche!
    ctx.push_obligation(ProofObligation::assert("same_size", "option_size == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Option<NonZero<u32>> same size as u32");
}

#[test]
fn struct_with_padding() {
    // struct { u8, u32 } = 1 + 3 padding + 4 = 8
    let mut ctx = VerificationContext::new();
    for v in &["u8_size", "padding", "u32_size", "total"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s1", "u8_size == 1"));
    ctx.push_obligation(ProofObligation::assume("pad", "padding == 3"));
    ctx.push_obligation(ProofObligation::assume("s2", "u32_size == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "t_def",
        "total == u8_size + padding + u32_size",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "total == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "u8 + padding + u32 = 8 bytes");
}

#[test]
fn zero_sized_type() {
    // PhantomData and () have size 0
    let mut ctx = VerificationContext::new();
    for v in &["zst_size", "array_of_zst"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("zs", "zst_size == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "aoz_def",
        "array_of_zst == zst_size * 100",
    ));
    ctx.push_obligation(ProofObligation::assert("still_zero", "array_of_zst == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "100 ZSTs = 0 bytes");
}

#[test]
fn repr_c_field_order() {
    // repr(C) guarantees field order matches declaration
    let mut ctx = VerificationContext::new();
    for v in &["offset_a", "offset_b", "offset_c"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("oa", "offset_a == 0"));
    ctx.push_obligation(ProofObligation::assume("ob", "offset_b == 4"));
    ctx.push_obligation(ProofObligation::assume("oc", "offset_c == 8"));
    ctx.push_obligation(ProofObligation::assert(
        "ordered",
        "offset_a < offset_b && offset_b < offset_c",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repr(C) fields in declaration order");
}
