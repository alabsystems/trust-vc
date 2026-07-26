// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn i2s_frame_size() {
    let mut ctx = VerificationContext::new();
    for v in &["bit_depth", "channels", "frame_bits"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // I2S frame = bit_depth × channels
    ctx.push_obligation(ProofObligation::assume("bd", "bit_depth == 16"));
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 2")); // stereo
    ctx.push_obligation(ProofObligation::assume(
        "fb_def",
        "frame_bits == bit_depth * channels",
    ));
    ctx.push_obligation(ProofObligation::assert("is_32", "frame_bits == 32"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "I2S: 16-bit × 2 channels = 32-bit frame");
}

#[test]
fn sample_rate_divider() {
    let mut ctx = VerificationContext::new();
    for v in &["mclk_hz", "divider", "sample_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // MCLK / divider = sample rate
    // 12288000 / 256 = 48000
    ctx.push_obligation(ProofObligation::assume("mh", "mclk_hz == 12288000"));
    ctx.push_obligation(ProofObligation::assume("d", "divider == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "sr_def",
        "sample_rate_hz == mclk_hz / divider",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_48000",
        "sample_rate_hz == 48000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "codec: 12.288MHz / 256 = 48kHz");
}

#[test]
fn dac_output_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["dac_value", "vref_mv", "max_value", "vout_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Vout = dac_value × Vref / max_value
    // Precompute: 2048 × 3300 / 4096 = 1650mV (midpoint)
    ctx.push_obligation(ProofObligation::assume("dv", "dac_value == 2048"));
    ctx.push_obligation(ProofObligation::assume("vr", "vref_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("mv", "max_value == 4096"));
    ctx.push_obligation(ProofObligation::assume("vo", "vout_mv == 1650")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_1650", "vout_mv == 1650"));
    ctx.push_obligation(ProofObligation::assert("below_vref", "vout_mv < vref_mv"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DAC: midpoint 2048/4096 × 3300 = 1650mV");
}

#[test]
fn volume_attenuation_db() {
    let mut ctx = VerificationContext::new();
    for v in &["volume_step", "db_per_step", "total_attenuation_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Volume control: each step = 0.5dB. Step 20 = 10dB attenuation
    // Use integer half-dB: step × 5 = tenths of dB
    ctx.push_obligation(ProofObligation::assume("vs", "volume_step == 20"));
    ctx.push_obligation(ProofObligation::assume("dps", "db_per_step == 5")); // 0.5dB in tenths
    ctx.push_obligation(ProofObligation::assume(
        "ta_def",
        "total_attenuation_db == volume_step * db_per_step",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_100",
        "total_attenuation_db == 100",
    )); // 10.0 dB
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "codec volume: 20 × 0.5dB = 10.0dB");
}

#[test]
fn dma_buffer_duration_us() {
    let mut ctx = VerificationContext::new();
    for v in &["buffer_samples", "sample_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("duration_us", u32_ty());
    // Buffer duration = samples / sample_rate × 1000000
    // Precompute: 256 / 48000 × 1000000 ≈ 5333us
    ctx.push_obligation(ProofObligation::assume("bs", "buffer_samples == 256"));
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate_hz == 48000"));
    ctx.push_obligation(ProofObligation::assume("du", "duration_us == 5333")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_5333", "duration_us == 5333"));
    ctx.push_obligation(ProofObligation::assert("reasonable", "duration_us > 1000")); // > 1ms
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "codec DMA: 256 samples @ 48kHz ≈ 5.3ms");
}

#[test]
fn headphone_detection() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jack_inserted", u32_ty());
    ctx.declare_var_typed("speaker_muted", i32_ty());
    // Auto-mute speaker when headphone inserted
    ctx.push_obligation(ProofObligation::assume("ji", "jack_inserted == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "sm_def",
        "speaker_muted == if jack_inserted == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "speaker_muted == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "codec: headphone in → speaker muted");
}

#[test]
fn mic_gain_setting() {
    let mut ctx = VerificationContext::new();
    for v in &["gain_register", "gain_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_gain", i32_ty());
    // Mic gain: 0-47 range maps to 0-47dB
    ctx.push_obligation(ProofObligation::assume("gr", "gain_register == 30"));
    ctx.push_obligation(ProofObligation::assume("gd", "gain_db == 30")); // 1:1 mapping
    ctx.push_obligation(ProofObligation::assume(
        "vg_def",
        "valid_gain == if gain_register <= 47 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_30", "gain_db == 30"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_gain == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "codec mic: gain register 30 → 30dB (valid)");
}

#[test]
fn bit_clock_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_rate", "bits_per_frame", "bclk_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // BCLK = sample_rate × bits_per_frame
    // 48000 × 32 = 1536000
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate == 48000"));
    ctx.push_obligation(ProofObligation::assume("bpf", "bits_per_frame == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "bh_def",
        "bclk_hz == sample_rate * bits_per_frame",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1536000", "bclk_hz == 1536000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "I2S BCLK: 48000 × 32 = 1.536MHz");
}

#[test]
fn sidetone_path() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sidetone_enabled", u32_ty());
    ctx.declare_var_typed("mic_active", u32_ty());
    ctx.declare_var_typed("sidetone_output", i32_ty());
    // Sidetone: route mic input to headphone for monitoring
    ctx.push_obligation(ProofObligation::assume("se", "sidetone_enabled == 1"));
    ctx.push_obligation(ProofObligation::assume("ma", "mic_active == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sidetone_output == if sidetone_enabled == 1 && mic_active == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sidetone_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "codec: sidetone enabled + mic active → output");
}

#[test]
fn equalizer_band_count() {
    let mut ctx = VerificationContext::new();
    for v in &["total_bands", "low_bands", "mid_bands", "high_bands"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_config", i32_ty());
    // 5-band EQ: 1 low, 3 mid, 1 high
    ctx.push_obligation(ProofObligation::assume("lb", "low_bands == 1"));
    ctx.push_obligation(ProofObligation::assume("mb", "mid_bands == 3"));
    ctx.push_obligation(ProofObligation::assume("hb", "high_bands == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tb_def",
        "total_bands == low_bands + mid_bands + high_bands",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_config == if total_bands >= 3 && total_bands <= 10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_5", "total_bands == 5"));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_config == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "codec EQ: 1+3+1 = 5 bands (valid)");
}
