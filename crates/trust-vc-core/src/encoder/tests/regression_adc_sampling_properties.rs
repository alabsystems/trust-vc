// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn nyquist_rate() {
    let mut ctx = VerificationContext::new();
    for v in &["signal_freq_hz", "sample_rate_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("above_nyquist", i32_ty());
    // Nyquist: sample rate must be > 2× signal frequency
    // Precompute: 2 × 5000 = 10000, sample_rate 44100 > 10000
    ctx.push_obligation(ProofObligation::assume("sf", "signal_freq_hz == 5000"));
    ctx.push_obligation(ProofObligation::assume("sr", "sample_rate_hz == 44100"));
    ctx.push_obligation(ProofObligation::assume("nyquist", "above_nyquist == 1")); // precomputed
    ctx.push_obligation(ProofObligation::assert("yes", "above_nyquist == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: 44100 > 2×5000 → above Nyquist (precomputed)");
}

#[test]
fn quantization_levels() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("adc_bits", u32_ty());
    ctx.declare_var_typed("num_levels", u32_ty());
    // Levels = 2^bits. Precompute: 2^12 = 4096
    ctx.push_obligation(ProofObligation::assume("ab", "adc_bits == 12"));
    ctx.push_obligation(ProofObligation::assume("nl", "num_levels == 4096")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_4096", "num_levels == 4096"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: 12-bit → 4096 quantization levels");
}

#[test]
fn oversampling_ratio() {
    let mut ctx = VerificationContext::new();
    for v in &["actual_rate", "target_rate", "osr"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // OSR = actual / target. Precompute: 256000 / 16000 = 16
    ctx.push_obligation(ProofObligation::assume("ar", "actual_rate == 256000"));
    ctx.push_obligation(ProofObligation::assume("tr", "target_rate == 16000"));
    ctx.push_obligation(ProofObligation::assume("osr_val", "osr == 16")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_16", "osr == 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: 256000/16000 = 16× oversampling");
}

#[test]
fn input_range_clipping() {
    let mut ctx = VerificationContext::new();
    for v in &["input_mv", "range_min_mv", "range_max_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("clipped", i32_ty());
    ctx.push_obligation(ProofObligation::assume("im", "input_mv == 3500"));
    ctx.push_obligation(ProofObligation::assume("rmn", "range_min_mv == 0"));
    ctx.push_obligation(ProofObligation::assume("rmx", "range_max_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume(
        "c_def",
        "clipped == if input_mv > range_max_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "clipped == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: 3500mV > 3300mV range → clipped");
}

#[test]
fn channel_mux_select() {
    let mut ctx = VerificationContext::new();
    for v in &["selected_channel", "num_channels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_channel", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sc", "selected_channel == 7"));
    ctx.push_obligation(ProofObligation::assume("nc", "num_channels == 16"));
    ctx.push_obligation(ProofObligation::assume(
        "vc_def",
        "valid_channel == if selected_channel < num_channels { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_channel == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: channel 7 < 16 total → valid");
}

#[test]
fn conversion_time_budget() {
    let mut ctx = VerificationContext::new();
    for v in &["sample_hold_us", "conversion_us", "total_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("within_budget", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sh", "sample_hold_us == 2"));
    ctx.push_obligation(ProofObligation::assume("cu", "conversion_us == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "tu_def",
        "total_us == sample_hold_us + conversion_us",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "wb_def",
        "within_budget == if total_us <= 20 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_12", "total_us == 12"));
    ctx.push_obligation(ProofObligation::assert("ok", "within_budget == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: 2us S/H + 10us conv = 12us ≤ 20us budget");
}

#[test]
fn dma_buffer_samples() {
    let mut ctx = VerificationContext::new();
    for v in &["buffer_bytes", "bytes_per_sample", "num_samples"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Samples in buffer = bytes / bytes_per_sample. Precompute: 1024 / 2 = 512
    ctx.push_obligation(ProofObligation::assume("bb", "buffer_bytes == 1024"));
    ctx.push_obligation(ProofObligation::assume("bps", "bytes_per_sample == 2"));
    ctx.push_obligation(ProofObligation::assume("ns", "num_samples == 512")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_512", "num_samples == 512"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC DMA: 1024 bytes / 2 per sample = 512 samples");
}

#[test]
fn differential_mode() {
    let mut ctx = VerificationContext::new();
    for v in &["pos_input_mv", "neg_input_mv", "diff_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // Differential: result = pos - neg
    ctx.push_obligation(ProofObligation::assume("pi", "pos_input_mv == 2000"));
    ctx.push_obligation(ProofObligation::assume("ni", "neg_input_mv == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "dm_def",
        "diff_mv == pos_input_mv - neg_input_mv",
    ));
    ctx.push_obligation(ProofObligation::assert("is_500", "diff_mv == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC differential: 2000mV - 1500mV = 500mV");
}

#[test]
fn averaging_filter_depth() {
    let mut ctx = VerificationContext::new();
    for v in &["filter_samples", "max_depth"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid_depth", i32_ty());
    // Hardware averaging: 1, 4, 8, 16, 32 samples typical
    ctx.push_obligation(ProofObligation::assume("fs", "filter_samples == 16"));
    ctx.push_obligation(ProofObligation::assume("md", "max_depth == 32"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "valid_depth == if filter_samples <= max_depth { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_depth == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: 16-sample averaging ≤ 32 max → valid depth");
}

#[test]
fn watchdog_threshold() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_value", "low_threshold", "high_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("out_of_window", i32_ty());
    // Analog watchdog: alert when value outside window
    ctx.push_obligation(ProofObligation::assume("av", "adc_value == 3800"));
    ctx.push_obligation(ProofObligation::assume("lt", "low_threshold == 1000"));
    ctx.push_obligation(ProofObligation::assume("ht", "high_threshold == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "oow_def",
        "out_of_window == if adc_value < low_threshold || adc_value > high_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "out_of_window == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC watchdog: 3800 > 3000 high threshold → alert");
}
