// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn tag_integer_low_bits() {
    // Tag integer with low 2 bits: val << 2 | tag
    let mut ctx = VerificationContext::new();
    for v in &["val", "tag", "tagged"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("v", "val == 10"));
    ctx.push_obligation(ProofObligation::assume("t", "tag == 1")); // int tag
    ctx.push_obligation(ProofObligation::assume(
        "tg_def",
        "tagged == (val << 2) | tag",
    ));
    // 10 << 2 = 40; 40 | 1 = 41
    ctx.push_obligation(ProofObligation::assert("is_41", "tagged == 41"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "tag int 10 with tag 1 → 41");
}

#[test]
fn extract_tag_from_tagged() {
    let mut ctx = VerificationContext::new();
    for v in &["tagged", "tag"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tg", "tagged == 41"));
    ctx.push_obligation(ProofObligation::assume("t_def", "tag == tagged & 3")); // low 2 bits
    ctx.push_obligation(ProofObligation::assert("is_1", "tag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "extract tag from 41: 41 & 3 = 1");
}

#[test]
fn extract_value_from_tagged() {
    let mut ctx = VerificationContext::new();
    for v in &["tagged", "val"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tg", "tagged == 41"));
    ctx.push_obligation(ProofObligation::assume("v_def", "val == tagged >> 2"));
    ctx.push_obligation(ProofObligation::assert("is_10", "val == 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "extract value from 41: 41 >> 2 = 10");
}

#[test]
fn tag_roundtrip() {
    let mut ctx = VerificationContext::new();
    for v in &["orig_val", "tag", "tagged", "recovered"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ov", "orig_val == 25"));
    ctx.push_obligation(ProofObligation::assume("t", "tag == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "tg_def",
        "tagged == (orig_val << 2) | tag",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "rec_def",
        "recovered == tagged >> 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "roundtrip",
        "recovered == orig_val",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "tag roundtrip: 25 → tagged → 25");
}

#[test]
fn discriminant_identifies_variant() {
    // Enum discriminant: 0=None, 1=Some
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discriminant", u32_ty());
    ctx.declare_var_typed("is_some", i32_ty());
    ctx.push_obligation(ProofObligation::assume("d", "discriminant == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_some == if discriminant == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("some", "is_some == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discriminant 1 → Some variant");
}

#[test]
fn pointer_alignment_tag() {
    // 8-byte aligned pointers have low 3 bits free for tags
    let mut ctx = VerificationContext::new();
    for v in &["ptr", "tag", "tagged_ptr", "extracted_ptr", "extracted_tag"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "ptr == 1024")); // aligned
    ctx.push_obligation(ProofObligation::assume("t", "tag == 5")); // tag in low 3 bits
    ctx.push_obligation(ProofObligation::assume("tp_def", "tagged_ptr == ptr | tag"));
    ctx.push_obligation(ProofObligation::assume(
        "ep_def",
        "extracted_ptr == tagged_ptr & 4294967288",
    )); // ~7
    ctx.push_obligation(ProofObligation::assume(
        "et_def",
        "extracted_tag == tagged_ptr & 7",
    ));
    ctx.push_obligation(ProofObligation::assert("ptr_ok", "extracted_ptr == 1024"));
    ctx.push_obligation(ProofObligation::assert("tag_ok", "extracted_tag == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pointer tag: 1024 | 5, extract both");
}

#[test]
fn small_integer_optimization() {
    // Small integers (< 256) can be stored inline in the tag word
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("val", u32_ty());
    ctx.declare_var_typed("is_inline", i32_ty());
    ctx.push_obligation(ProofObligation::assume("v", "val == 42"));
    ctx.push_obligation(ProofObligation::assume(
        "ii_def",
        "is_inline == if val < 256 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("inline", "is_inline == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "42 < 256 → inline small int");
}

#[test]
fn niche_optimization_bool() {
    // Bool uses niche: only values 0 and 1, so 2+ can encode None
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("raw_val", u32_ty());
    ctx.declare_var_typed("is_none", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rv", "raw_val == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "in_def",
        "is_none == if raw_val > 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("none", "is_none == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bool niche: 2 → None");
}

#[test]
fn tag_bits_count() {
    // 2 tag bits → 4 possible type tags
    let mut ctx = VerificationContext::new();
    for v in &["tag_bits", "max_tags"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("tb", "tag_bits == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "mt_def",
        "max_tags == 1 << tag_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "max_tags == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "2 tag bits → 4 possible tags");
}

#[test]
fn null_pointer_representation() {
    // NULL is all-zero, which is tag 0 + value 0
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("raw", u32_ty());
    ctx.declare_var_typed("is_null", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "raw == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "in_def",
        "is_null == if raw == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("null", "is_null == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "0 → null pointer");
}
