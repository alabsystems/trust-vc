// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn vector_register_width() {
    let mut ctx = VerificationContext::new();
    for v in &["elements", "element_bits", "register_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 128-bit SIMD: 4 × 32-bit elements
    ctx.push_obligation(ProofObligation::assume("e", "elements == 4"));
    ctx.push_obligation(ProofObligation::assume("eb", "element_bits == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "rb_def",
        "register_bits == elements * element_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_128", "register_bits == 128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SIMD: 4 × 32 = 128-bit register");
}

#[test]
fn lane_count_from_width() {
    let mut ctx = VerificationContext::new();
    for v in &["register_bits", "element_bits", "lanes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 256-bit AVX / 64-bit doubles = 4 lanes
    ctx.push_obligation(ProofObligation::assume("rb", "register_bits == 256"));
    ctx.push_obligation(ProofObligation::assume("eb", "element_bits == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "l_def",
        "lanes == register_bits / element_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "lanes == 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SIMD: 256 / 64 = 4 double lanes");
}

#[test]
fn saturating_add_u8() {
    let mut ctx = VerificationContext::new();
    for v in &["a", "b", "raw_sum"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("result", u32_ty());
    // Saturating add: min(a + b, 255)
    ctx.push_obligation(ProofObligation::assume("av", "a == 200"));
    ctx.push_obligation(ProofObligation::assume("bv", "b == 100"));
    ctx.push_obligation(ProofObligation::assume("rs_def", "raw_sum == a + b"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == if raw_sum > 255 { 255 } else { raw_sum }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_255", "result == 255")); // 300 → 255
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIMD sat add: 200 + 100 = 300 → clamp 255");
}

#[test]
fn vector_alignment() {
    let mut ctx = VerificationContext::new();
    for v in &["address", "alignment"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("aligned", i32_ty());
    // AVX-256 requires 32-byte alignment
    ctx.push_obligation(ProofObligation::assume("a", "address == 1024")); // 0x400
    ctx.push_obligation(ProofObligation::assume("al", "alignment == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "al_def",
        "aligned == if address % alignment == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "aligned == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SIMD: 1024 % 32 == 0 → aligned");
}

#[test]
fn shuffle_mask_validity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mask_value", u32_ty());
    ctx.declare_var_typed("max_index", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Shuffle mask index must be < lane count
    ctx.push_obligation(ProofObligation::assume("mv", "mask_value == 3"));
    ctx.push_obligation(ProofObligation::assume("mi", "max_index == 4")); // 4 lanes
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if mask_value < max_index { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIMD shuffle: mask 3 < 4 lanes → valid");
}

#[test]
fn horizontal_add_pairs() {
    let mut ctx = VerificationContext::new();
    for v in &["a0", "a1", "a2", "a3", "sum01", "sum23"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Horizontal add: pairwise sum of adjacent elements
    ctx.push_obligation(ProofObligation::assume("a0v", "a0 == 10"));
    ctx.push_obligation(ProofObligation::assume("a1v", "a1 == 20"));
    ctx.push_obligation(ProofObligation::assume("a2v", "a2 == 30"));
    ctx.push_obligation(ProofObligation::assume("a3v", "a3 == 40"));
    ctx.push_obligation(ProofObligation::assume("s01_def", "sum01 == a0 + a1"));
    ctx.push_obligation(ProofObligation::assume("s23_def", "sum23 == a2 + a3"));
    ctx.push_obligation(ProofObligation::assert("is_30", "sum01 == 30"));
    ctx.push_obligation(ProofObligation::assert("is_70", "sum23 == 70"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIMD hadd: [10,20,30,40] → [30, 70]");
}

#[test]
fn blend_mask_selection() {
    let mut ctx = VerificationContext::new();
    for v in &["src_a", "src_b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("result", u32_ty());
    ctx.declare_var_typed("mask_bit", u32_ty());
    // Blend: select from A or B based on mask bit
    ctx.push_obligation(ProofObligation::assume("sa", "src_a == 100"));
    ctx.push_obligation(ProofObligation::assume("sb", "src_b == 200"));
    ctx.push_obligation(ProofObligation::assume("mb", "mask_bit == 1")); // select B
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == if mask_bit == 1 { src_b } else { src_a }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_200", "result == 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIMD blend: mask=1 → select B (200)");
}

#[test]
fn vector_throughput() {
    let mut ctx = VerificationContext::new();
    for v in &["scalar_ops", "vector_width", "vector_ops"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("speedup_valid", i32_ty());
    // Vectorization: N scalar ops → N/width vector ops
    // 1024 ops / 8 lanes = 128 vector ops
    ctx.push_obligation(ProofObligation::assume("so", "scalar_ops == 1024"));
    ctx.push_obligation(ProofObligation::assume("vw", "vector_width == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vector_ops == scalar_ops / vector_width",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "sv_def",
        "speedup_valid == if vector_ops < scalar_ops { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_128", "vector_ops == 128"));
    ctx.push_obligation(ProofObligation::assert("ok", "speedup_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "SIMD: 1024 / 8 = 128 vector ops");
}

#[test]
fn mask_register_popcount() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mask_value", u32_ty());
    ctx.declare_var_typed("active_lanes", u32_ty());
    ctx.declare_var_typed("all_active", i32_ty());
    // Mask register with 8 lanes, value 0xFF means all active
    // Precompute popcount
    ctx.push_obligation(ProofObligation::assume("mv", "mask_value == 255")); // 0xFF
    ctx.push_obligation(ProofObligation::assume("al", "active_lanes == 8")); // precomputed popcount
    ctx.push_obligation(ProofObligation::assume(
        "aa_def",
        "all_active == if active_lanes == 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_8", "active_lanes == 8"));
    ctx.push_obligation(ProofObligation::assert("yes", "all_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIMD mask: 0xFF → 8 active lanes (all)");
}

#[test]
fn gather_stride() {
    let mut ctx = VerificationContext::new();
    for v in &["base_addr", "index", "stride", "element_addr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Gather: addr = base + index × stride
    // Precompute: 4096 + 3 × 8 = 4096 + 24 = 4120
    ctx.push_obligation(ProofObligation::assume("ba", "base_addr == 4096"));
    ctx.push_obligation(ProofObligation::assume("i", "index == 3"));
    ctx.push_obligation(ProofObligation::assume("s", "stride == 8"));
    ctx.push_obligation(ProofObligation::assume("ea", "element_addr == 4120")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_4120", "element_addr == 4120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "SIMD gather: 4096 + 3×8 = 4120");
}
