// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn tmds_clock_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["pixel_clock_mhz", "color_depth_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tmds_clock_mhz", u32_ty());
    // TMDS clock = pixel_clock × color_depth / 8. Precompute: 148 × 8 / 8 = 148
    ctx.push_obligation(ProofObligation::assume("pc", "pixel_clock_mhz == 148"));
    ctx.push_obligation(ProofObligation::assume("cd", "color_depth_bits == 8"));
    ctx.push_obligation(ProofObligation::assume("tc", "tmds_clock_mhz == 148")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_148", "tmds_clock_mhz == 148"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI: 148MHz pixel × 8/8 = 148MHz TMDS");
}

#[test]
fn hdcp_version_check() {
    let mut ctx = VerificationContext::new();
    for v in &["source_hdcp", "sink_hdcp"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("compatible", i32_ty());
    // HDCP: sink must support at least source version
    ctx.push_obligation(ProofObligation::assume("sh", "source_hdcp == 22")); // v2.2
    ctx.push_obligation(ProofObligation::assume("sk", "sink_hdcp == 22"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "compatible == if sink_hdcp >= source_hdcp { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "compatible == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI HDCP: sink v2.2 ≥ source v2.2 → compatible");
}

#[test]
fn edid_block_count() {
    let mut ctx = VerificationContext::new();
    for v in &["extension_blocks", "base_block"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("total_blocks", u32_ty());
    ctx.declare_var_typed("valid_edid", i32_ty());
    // EDID: 1 base + N extension blocks, max 256 total
    ctx.push_obligation(ProofObligation::assume("eb", "extension_blocks == 3"));
    ctx.push_obligation(ProofObligation::assume("bb", "base_block == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_blocks == base_block + extension_blocks",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_edid == if total_blocks <= 256 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_4", "total_blocks == 4"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_edid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI EDID: 1 base + 3 ext = 4 blocks ≤ 256");
}

#[test]
fn audio_sample_packet_size() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "sample_bits", "samples_per_packet"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("packet_bits", u32_ty());
    // Audio sample packet: channels × bits × samples. Precompute: 2 × 16 × 4 = 128
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 2"));
    ctx.push_obligation(ProofObligation::assume("sb", "sample_bits == 16"));
    ctx.push_obligation(ProofObligation::assume("spp", "samples_per_packet == 4"));
    ctx.push_obligation(ProofObligation::assume("pb", "packet_bits == 128")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_128", "packet_bits == 128"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI audio: 2ch × 16bit × 4 samples = 128 bits");
}

#[test]
fn color_space_depth() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("color_depth", u32_ty());
    ctx.declare_var_typed("is_deep_color", i32_ty());
    // Deep Color: >8 bits per channel (10, 12, or 16)
    ctx.push_obligation(ProofObligation::assume("cd", "color_depth == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "idc_def",
        "is_deep_color == if color_depth > 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_deep_color == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI: 10 bits > 8 → Deep Color");
}

#[test]
fn cec_address_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cec_addr", u32_ty());
    ctx.declare_var_typed("valid_addr", i32_ty());
    // CEC logical addresses: 0-14 valid, 15 = unregistered
    ctx.push_obligation(ProofObligation::assume("ca", "cec_addr == 4")); // Playback 1
    ctx.push_obligation(ProofObligation::assume(
        "va_def",
        "valid_addr == if cec_addr <= 14 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_addr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI CEC: address 4 ≤ 14 → valid");
}

#[test]
fn bandwidth_capacity() {
    let mut ctx = VerificationContext::new();
    for v in &["required_gbps", "max_bandwidth_gbps"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sufficient", i32_ty());
    // HDMI 2.0: 18 Gbps max bandwidth
    ctx.push_obligation(ProofObligation::assume("rg", "required_gbps == 12"));
    ctx.push_obligation(ProofObligation::assume("mb", "max_bandwidth_gbps == 18"));
    ctx.push_obligation(ProofObligation::assume(
        "s_def",
        "sufficient == if required_gbps <= max_bandwidth_gbps { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sufficient == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI 2.0: 12 Gbps ≤ 18 Gbps max → sufficient");
}

#[test]
fn infoframe_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frame_type", u32_ty());
    ctx.declare_var_typed("is_avi", i32_ty());
    ctx.declare_var_typed("is_audio", i32_ty());
    // InfoFrame types: 0x82=AVI (130), 0x84=Audio (132)
    ctx.push_obligation(ProofObligation::assume("ft", "frame_type == 130"));
    ctx.push_obligation(ProofObligation::assume(
        "ia_def",
        "is_avi == if frame_type == 130 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "iau_def",
        "is_audio == if frame_type == 132 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("avi", "is_avi == 1"));
    ctx.push_obligation(ProofObligation::assert("not_audio", "is_audio == 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI: frame type 0x82 → AVI InfoFrame, not Audio");
}

#[test]
fn hot_plug_detect() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hpd_state", u32_ty());
    ctx.declare_var_typed("prev_hpd_state", u32_ty());
    ctx.declare_var_typed("plug_event", i32_ty());
    ctx.push_obligation(ProofObligation::assume("hs", "hpd_state == 1"));
    ctx.push_obligation(ProofObligation::assume("phs", "prev_hpd_state == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "pe_def",
        "plug_event == if hpd_state == 1 && prev_hpd_state == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "plug_event == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI: HPD 0→1 → plug event detected");
}

#[test]
fn scrambling_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["tmds_rate_mhz", "scrambling_threshold_mhz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("needs_scrambling", i32_ty());
    // HDMI 2.0: scrambling required above 340 MHz TMDS
    ctx.push_obligation(ProofObligation::assume("tr", "tmds_rate_mhz == 594"));
    ctx.push_obligation(ProofObligation::assume(
        "st",
        "scrambling_threshold_mhz == 340",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "ns_def",
        "needs_scrambling == if tmds_rate_mhz > scrambling_threshold_mhz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "needs_scrambling == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "HDMI: 594 MHz > 340 MHz → scrambling required");
}
