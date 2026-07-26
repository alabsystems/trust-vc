// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn rgb_channel_range() {
    // Each RGB channel is 0-255
    let mut ctx = VerificationContext::new();
    for v in &["r", "g", "b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 128"));
    ctx.push_obligation(ProofObligation::assume("g_val", "g == 64"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 255"));
    ctx.push_obligation(ProofObligation::assert(
        "in_range",
        "r <= 255 && g <= 255 && b <= 255",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RGB channels in [0, 255]");
}

#[test]
fn pack_rgb_to_u32() {
    // Pack RGB into single u32: (r << 16) | (g << 8) | b
    let mut ctx = VerificationContext::new();
    for v in &["r", "g", "b", "packed"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 255"));
    ctx.push_obligation(ProofObligation::assume("g_val", "g == 128"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "packed == (r << 16) | (g << 8) | b",
    ));
    // 255*65536 + 128*256 + 0 = 16744448 + 32768 = 16777216? No.
    // 255 << 16 = 16711680, 128 << 8 = 32768, 0 = 0
    // 16711680 | 32768 | 0 = 16744448
    ctx.push_obligation(ProofObligation::assert("is_packed", "packed == 16744448"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "pack RGB(255,128,0) = 16744448");
}

#[test]
fn unpack_red_channel() {
    let mut ctx = VerificationContext::new();
    for v in &["packed", "r"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("p", "packed == 16744448"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "r == (packed >> 16) & 255",
    ));
    ctx.push_obligation(ProofObligation::assert("is_255", "r == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "unpack red from 16744448 = 255");
}

#[test]
fn alpha_blend_halfway() {
    // Alpha blend: result = src * alpha + dst * (256 - alpha) / 256
    // With alpha=128 (50%): result ≈ (src + dst) / 2
    let mut ctx = VerificationContext::new();
    for v in &["src", "dst", "alpha", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("s", "src == 200"));
    ctx.push_obligation(ProofObligation::assume("d", "dst == 100"));
    ctx.push_obligation(ProofObligation::assume("a", "alpha == 128"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == (src * alpha + dst * (256 - alpha)) / 256",
    ));
    // (200*128 + 100*128) / 256 = (25600 + 12800) / 256 = 38400/256 = 150
    ctx.push_obligation(ProofObligation::assert("is_150", "result == 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "alpha blend 50%: (200+100)/2 = 150");
}

#[test]
fn grayscale_luminance() {
    // Approximate grayscale: (r*77 + g*150 + b*29) / 256
    let mut ctx = VerificationContext::new();
    for v in &["r", "g", "b", "gray"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 255"));
    ctx.push_obligation(ProofObligation::assume("g_val", "g == 255"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "gray_def",
        "gray == (r * 77 + g * 150 + b * 29) / 256",
    ));
    // (255*77 + 255*150 + 255*29) / 256 = 255*256/256 = 255
    ctx.push_obligation(ProofObligation::assert("white_is_255", "gray == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "grayscale(white) = 255");
}

#[test]
fn clamp_channel() {
    let mut ctx = VerificationContext::new();
    for v in &["raw", "clamped"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r", "raw == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "cl_def",
        "clamped == if raw > 255 { 255 } else { raw }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_255", "clamped == 255"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "clamp(300) = 255");
}

#[test]
fn invert_color() {
    // Invert: 255 - channel
    let mut ctx = VerificationContext::new();
    for v in &["r", "inv_r"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 200"));
    ctx.push_obligation(ProofObligation::assume("inv_def", "inv_r == 255 - r"));
    ctx.push_obligation(ProofObligation::assert("is_55", "inv_r == 55"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "invert(200) = 55");
}

#[test]
fn double_invert_identity() {
    let mut ctx = VerificationContext::new();
    for v in &["r", "inv1", "inv2"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("r_val", "r == 100"));
    ctx.push_obligation(ProofObligation::assume("i1_def", "inv1 == 255 - r"));
    ctx.push_obligation(ProofObligation::assume("i2_def", "inv2 == 255 - inv1"));
    ctx.push_obligation(ProofObligation::assert("roundtrip", "inv2 == r"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "invert(invert(100)) = 100");
}

#[test]
fn hex_color_component_extraction() {
    // 0xFF8040: R=0xFF=255, G=0x80=128, B=0x40=64
    let mut ctx = VerificationContext::new();
    for v in &["hex", "r", "g", "b"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("h", "hex == 16744512"));
    ctx.push_obligation(ProofObligation::assume("r_def", "r == (hex >> 16) & 255"));
    ctx.push_obligation(ProofObligation::assume("g_def", "g == (hex >> 8) & 255"));
    ctx.push_obligation(ProofObligation::assume("b_def", "b == hex & 255"));
    ctx.push_obligation(ProofObligation::assert("r_is_255", "r == 255"));
    ctx.push_obligation(ProofObligation::assert("g_is_128", "g == 128"));
    ctx.push_obligation(ProofObligation::assert("b_is_64", "b == 64"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "0xFF8040 → R=255, G=128, B=64");
}

#[test]
fn brightness_adjustment() {
    // Increase brightness: min(channel + delta, 255)
    let mut ctx = VerificationContext::new();
    for v in &["channel", "delta", "result"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ch", "channel == 200"));
    ctx.push_obligation(ProofObligation::assume("d", "delta == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "r_def",
        "result == if channel + delta > 255 { 255 } else { channel + delta }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_230", "result == 230"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "brighten(200, 30) = 230");
}
