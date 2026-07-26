// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn channel_value() {
    let mut ctx = VerificationContext::new();
    for v in &["value", "max_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    // DMX channel: 8-bit, 0-255
    ctx.push_obligation(ProofObligation::assume("v", "value == 200"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_value == 255"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if value <= max_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: value 200 ≤ 255 → valid channel data");
}

#[test]
fn universe_channels() {
    let mut ctx = VerificationContext::new();
    for v in &["channel", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_valid", i32_ty());
    // DMX512: 512 channels per universe (1-512)
    ctx.push_obligation(ProofObligation::assume("c", "channel == 256"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_channels == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "cv_def",
        "ch_valid == if channel >= 1 && channel <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ch_valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: channel 256 in [1, 512] → valid");
}

#[test]
fn baud_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("baud", u32_ty());
    ctx.declare_var_typed("is_standard", i32_ty());
    // DMX512 baud rate: 250kbps
    ctx.push_obligation(ProofObligation::assume("b", "baud == 250000"));
    ctx.push_obligation(ProofObligation::assume(
        "is_def",
        "is_standard == if baud == 250000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_standard == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: baud=250000 → standard rate");
}

#[test]
fn break_time() {
    let mut ctx = VerificationContext::new();
    for v in &["break_us", "min_break_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("break_ok", i32_ty());
    // DMX break: minimum 88μs (22 bit times at 250kbps)
    ctx.push_obligation(ProofObligation::assume("bu", "break_us == 100"));
    ctx.push_obligation(ProofObligation::assume("mb", "min_break_us == 88"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "break_ok == if break_us >= min_break_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "break_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: 100μs break ≥ 88μs min → OK");
}

#[test]
fn mark_after_break() {
    let mut ctx = VerificationContext::new();
    for v in &["mab_us", "min_mab_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mab_ok", i32_ty());
    // Mark After Break: minimum 8μs (2 bit times)
    ctx.push_obligation(ProofObligation::assume("mu", "mab_us == 12"));
    ctx.push_obligation(ProofObligation::assume("mm", "min_mab_us == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "mo_def",
        "mab_ok == if mab_us >= min_mab_us { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "mab_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: 12μs MAB ≥ 8μs min → OK");
}

#[test]
fn fixture_start_address() {
    let mut ctx = VerificationContext::new();
    for v in &["start_addr", "fixture_channels", "universe_size"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fits", i32_ty());
    // Fixture must fit within universe: start + channels - 1 ≤ 512
    ctx.push_obligation(ProofObligation::assume("sa", "start_addr == 100"));
    ctx.push_obligation(ProofObligation::assume("fc", "fixture_channels == 16"));
    ctx.push_obligation(ProofObligation::assume("us", "universe_size == 512"));
    ctx.push_obligation(ProofObligation::assume(
        "f_def",
        "fits == if start_addr + fixture_channels <= universe_size + 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fits == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: fixture 100+16 ≤ 513 → fits in universe");
}

#[test]
fn refresh_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["refresh_hz", "min_refresh_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("refresh_ok", i32_ty());
    // Full 512-channel frame: ~44Hz max at 250kbps
    ctx.push_obligation(ProofObligation::assume("rh", "refresh_hz == 40"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_refresh_hz == 25"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "refresh_ok == if refresh_hz >= min_refresh_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "refresh_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: 40Hz refresh ≥ 25Hz min → OK");
}

#[test]
fn cable_length() {
    let mut ctx = VerificationContext::new();
    for v in &["length_m", "max_length_m"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("length_ok", i32_ty());
    // DMX512: max 300m per run (RS-485 physical layer)
    ctx.push_obligation(ProofObligation::assume("lm", "length_m == 150"));
    ctx.push_obligation(ProofObligation::assume("ml", "max_length_m == 300"));
    ctx.push_obligation(ProofObligation::assume(
        "lo_def",
        "length_ok == if length_m <= max_length_m { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "length_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: 150m cable ≤ 300m max → OK");
}

#[test]
fn universe_count() {
    let mut ctx = VerificationContext::new();
    for v in &["universes", "max_universes"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("uni_ok", i32_ty());
    // Multi-universe: Art-Net/sACN supports thousands
    ctx.push_obligation(ProofObligation::assume("u", "universes == 4"));
    ctx.push_obligation(ProofObligation::assume("mu", "max_universes == 64"));
    ctx.push_obligation(ProofObligation::assume(
        "uo_def",
        "uni_ok == if universes <= max_universes { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "uni_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: 4 universes ≤ 64 max → OK");
}

#[test]
fn dimming_curve() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curve_type", u32_ty());
    ctx.declare_var_typed("is_linear", i32_ty());
    // Dimming curves: 0=linear, 1=square, 2=S-curve, 3=IES
    ctx.push_obligation(ProofObligation::assume("ct", "curve_type == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "il_def",
        "is_linear == if curve_type == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_linear == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DMX512: curve_type=0 → linear dimming");
}
