// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn sample_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_hz", u32_ty());
    ctx.declare_var_typed("valid_rate", i32_ty());
    // Standard audio rates: 8000, 16000, 22050, 32000, 44100, 48000, 96000, 192000
    ctx.push_obligation(ProofObligation::assume("rh", "rate_hz == 48000"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_rate == if rate_hz == 8000 || rate_hz == 16000 || rate_hz == 44100 || rate_hz == 48000 || rate_hz == 96000 || rate_hz == 192000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_rate == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: 48000 Hz is valid sample rate");
}

#[test]
fn bit_depth() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bits", u32_ty());
    ctx.declare_var_typed("valid_depth", i32_ty());
    // I2S bit depth: 16, 24, 32
    ctx.push_obligation(ProofObligation::assume("b", "bits == 24"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_depth == if bits == 16 || bits == 24 || bits == 32 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_depth == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: 24-bit depth is valid");
}

#[test]
fn mclk_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["mclk_hz", "fs_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("mclk_ratio", u32_ty());
    // MCLK = N × Fs. Precompute: 12288000 / 48000 = 256
    ctx.push_obligation(ProofObligation::assume("mh", "mclk_hz == 12288000"));
    ctx.push_obligation(ProofObligation::assume("fh", "fs_hz == 48000"));
    ctx.push_obligation(ProofObligation::assume("mr", "mclk_ratio == 256")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_256", "mclk_ratio == 256"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: 12.288MHz / 48kHz = 256× MCLK (precomputed)");
}

#[test]
fn channel_count() {
    let mut ctx = VerificationContext::new();
    for v in &["channels", "max_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("ch_ok", i32_ty());
    // I2S: 2 channels (stereo), TDM: up to 8 or 16
    ctx.push_obligation(ProofObligation::assume("c", "channels == 2"));
    ctx.push_obligation(ProofObligation::assume("mc", "max_channels == 8"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "ch_ok == if channels <= max_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "ch_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: 2 channels ≤ 8 max → OK");
}

#[test]
fn bclk_frequency() {
    let mut ctx = VerificationContext::new();
    for v in &["bclk_hz", "max_bclk_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bclk_ok", i32_ty());
    // BCLK = Fs × bits × channels. Check within interface limits.
    ctx.push_obligation(ProofObligation::assume("bh", "bclk_hz == 3072000")); // 48000×32×2
    ctx.push_obligation(ProofObligation::assume("mb", "max_bclk_hz == 25000000")); // 25MHz
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bclk_ok == if bclk_hz <= max_bclk_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bclk_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: 3.072MHz BCLK ≤ 25MHz max → OK");
}

#[test]
fn data_format() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("format", u32_ty());
    ctx.declare_var_typed("is_i2s", i32_ty());
    // Formats: 0=I2S (standard), 1=left-justified, 2=right-justified, 3=DSP/PCM
    ctx.push_obligation(ProofObligation::assume("f", "format == 0"));
    ctx.push_obligation(ProofObligation::assume(
        "ii_def",
        "is_i2s == if format == 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_i2s == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: format=0 → standard I2S");
}

#[test]
fn ws_polarity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ws", u32_ty());
    ctx.declare_var_typed("is_right", i32_ty());
    // Word Select: 0=left channel, 1=right channel
    ctx.push_obligation(ProofObligation::assume("w", "ws == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "is_right == if ws == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "is_right == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: WS=1 → right channel");
}

#[test]
fn fifo_level() {
    let mut ctx = VerificationContext::new();
    for v in &["fifo_samples", "max_fifo"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("fifo_ok", i32_ty());
    // Audio FIFO buffer level
    ctx.push_obligation(ProofObligation::assume("fs", "fifo_samples == 64"));
    ctx.push_obligation(ProofObligation::assume("mf", "max_fifo == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "fo_def",
        "fifo_ok == if fifo_samples <= max_fifo { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "fifo_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: 64 FIFO samples ≤ 256 max → OK");
}

#[test]
fn dynamic_range() {
    let mut ctx = VerificationContext::new();
    for v in &["snr_db", "min_snr_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("snr_ok", i32_ty());
    // DAC/ADC SNR: 24-bit theoretical = 144dB, practical ~110-120dB
    ctx.push_obligation(ProofObligation::assume("sd", "snr_db == 115"));
    ctx.push_obligation(ProofObligation::assume("ms", "min_snr_db == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "snr_ok == if snr_db >= min_snr_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "snr_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: 115dB SNR ≥ 100dB min → dynamic range OK");
}

#[test]
fn clock_master_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("is_master", u32_ty());
    ctx.declare_var_typed("generates_clk", i32_ty());
    // Master generates BCLK and WS; slave receives them
    ctx.push_obligation(ProofObligation::assume("im", "is_master == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "gc_def",
        "generates_clk == if is_master == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "generates_clk == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "I2S: master=1 → generates BCLK/WS");
}
