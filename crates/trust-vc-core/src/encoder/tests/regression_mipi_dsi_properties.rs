// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn lane_count() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lanes", u32_ty());
    ctx.declare_var_typed("valid_lanes", i32_ty());
    // MIPI DSI: 1, 2, 3, or 4 data lanes
    ctx.push_obligation(ProofObligation::assume("l", "lanes == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vl_def",
        "valid_lanes == if lanes >= 1 && lanes <= 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_lanes == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: 4 lanes in [1, 4] → valid");
}

#[test]
fn hs_bitrate() {
    let mut ctx = VerificationContext::new();
    for v in &["bitrate_mbps", "max_bitrate_mbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rate_ok", i32_ty());
    // High-speed mode: up to 1.5 Gbps/lane (DSI-2: up to 4.5 Gbps)
    ctx.push_obligation(ProofObligation::assume("bm", "bitrate_mbps == 1000"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_bitrate_mbps == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rate_ok == if bitrate_mbps <= max_bitrate_mbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rate_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: 1000 Mbps ≤ 1500 max → rate OK");
}

#[test]
fn pixel_format() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bpp", u32_ty());
    ctx.declare_var_typed("valid_format", i32_ty());
    // Bits per pixel: 16 (RGB565), 18 (RGB666), 24 (RGB888)
    ctx.push_obligation(ProofObligation::assume("b", "bpp == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_format == if bpp == 16 || bpp == 18 || bpp == 24 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_format == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: 24 bpp (RGB888) is valid format");
}

#[test]
fn video_mode_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.declare_var_typed("is_burst", i32_ty());
    // Video modes: 0=non-burst sync pulse, 1=non-burst sync event, 2=burst
    ctx.push_obligation(ProofObligation::assume("m", "mode == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "ib_def",
        "is_burst == if mode == 2 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_burst == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: mode=2 → burst video mode");
}

#[test]
fn horizontal_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["h_pixels", "max_h_pixels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("h_ok", i32_ty());
    // Horizontal resolution
    ctx.push_obligation(ProofObligation::assume("hp", "h_pixels == 1080"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_h_pixels == 2560"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "h_ok == if h_pixels <= max_h_pixels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "h_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: 1080px width ≤ 2560 max → OK");
}

#[test]
fn vertical_resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["v_pixels", "max_v_pixels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("v_ok", i32_ty());
    // Vertical resolution
    ctx.push_obligation(ProofObligation::assume("vp", "v_pixels == 1920"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_v_pixels == 2560"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "v_ok == if v_pixels <= max_v_pixels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "v_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: 1920px height ≤ 2560 max → OK");
}

#[test]
fn lp_clock() {
    let mut ctx = VerificationContext::new();
    for v in &["lp_mhz", "min_lp_mhz", "max_lp_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("lp_ok", i32_ty());
    // Low-power clock: 1-20 MHz
    ctx.push_obligation(ProofObligation::assume("lm", "lp_mhz == 10"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_lp_mhz == 1"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_lp_mhz == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "lp_ok == if lp_mhz >= min_lp_mhz && lp_mhz <= max_lp_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "lp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: LP 10MHz in [1, 20] → OK");
}

#[test]
fn blanking_packet_size() {
    let mut ctx = VerificationContext::new();
    for v in &["blank_bytes", "max_blank_bytes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("blank_ok", i32_ty());
    // Blanking (null) packet padding in burst mode
    ctx.push_obligation(ProofObligation::assume("bb", "blank_bytes == 200"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_blank_bytes == 1024"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "blank_ok == if blank_bytes <= max_blank_bytes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "blank_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: 200B blanking ≤ 1024B max → OK");
}

#[test]
fn ecc_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ecc_enabled", u32_ty());
    ctx.declare_var_typed("header_protected", i32_ty());
    // ECC on packet header (single-bit correction, multi-bit detection)
    ctx.push_obligation(ProofObligation::assume("ee", "ecc_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "hp_def",
        "header_protected == if ecc_enabled == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "header_protected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: ECC=1 → header protected");
}

#[test]
fn virtual_channel() {
    let mut ctx = VerificationContext::new();
    for v in &["vc_id", "max_vc_id"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("vc_ok", i32_ty());
    // Virtual channel ID: 0-3 (2 bits)
    ctx.push_obligation(ProofObligation::assume("vi", "vc_id == 0"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_vc_id == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "vc_ok == if vc_id <= max_vc_id { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "vc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "MIPI DSI: VC 0 ≤ 3 → valid virtual channel");
}
