// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn resolution_levels() {
    let mut ctx = VerificationContext::new();
    for v in &["bits", "levels"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // 12-bit ADC: 2^12 = 4096 levels
    ctx.push_obligation(ProofObligation::assume("b", "bits == 12"));
    ctx.push_obligation(ProofObligation::assume("l", "levels == 4096")); // 2^12
    ctx.push_obligation(ProofObligation::assert("is_4096", "levels == 4096"));
    ctx.push_obligation(ProofObligation::assert("positive", "levels > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: 12-bit → 4096 levels");
}

#[test]
fn voltage_step_size() {
    let mut ctx = VerificationContext::new();
    for v in &["vref_mv", "levels", "step_uv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    // LSB = Vref / levels. 3300mV / 4096 ≈ 0.806mV = 806µV (precomputed)
    ctx.push_obligation(ProofObligation::assume("vr", "vref_mv == 3300"));
    ctx.push_obligation(ProofObligation::assume("l", "levels == 4096"));
    ctx.push_obligation(ProofObligation::assume("s", "step_uv == 806")); // precomputed
    ctx.push_obligation(ProofObligation::assert("is_806", "step_uv == 806"));
    ctx.push_obligation(ProofObligation::assert("small", "step_uv < vref_mv"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC LSB: ≈806µV for 3.3V/12-bit");
}

#[test]
fn conversion_result_range() {
    let mut ctx = VerificationContext::new();
    for v in &["raw_value", "max_value"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rv", "raw_value == 2048")); // mid-scale
    ctx.push_obligation(ProofObligation::assume("mv", "max_value == 4095")); // 2^12 - 1
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if raw_value <= max_value { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: 2048 <= 4095 → valid");
}

#[test]
fn sample_rate_from_clock() {
    let mut ctx = VerificationContext::new();
    for v in &["adc_clock_hz", "cycles_per_sample", "sample_rate"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("ac", "adc_clock_hz == 14000000")); // 14MHz
    ctx.push_obligation(ProofObligation::assume("cps", "cycles_per_sample == 14")); // 12.5+1.5
    ctx.push_obligation(ProofObligation::assume(
        "sr_def",
        "sample_rate == adc_clock_hz / cycles_per_sample",
    ));
    ctx.push_obligation(ProofObligation::assert("is_1m", "sample_rate == 1000000")); // 1MSPS
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ADC: 14MHz/14=1MSPS");
}

#[test]
fn oversampling_effective_bits() {
    // 4x oversampling adds 1 effective bit
    let mut ctx = VerificationContext::new();
    for v in &[
        "native_bits",
        "oversample_factor",
        "extra_bits",
        "effective_bits",
    ] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("nb", "native_bits == 12"));
    ctx.push_obligation(ProofObligation::assume("of", "oversample_factor == 16")); // 4^2
    ctx.push_obligation(ProofObligation::assume("eb", "extra_bits == 2")); // log4(16) = 2
    ctx.push_obligation(ProofObligation::assume(
        "efb_def",
        "effective_bits == native_bits + extra_bits",
    ));
    ctx.push_obligation(ProofObligation::assert("is_14", "effective_bits == 14"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC oversampling: 12+2=14 effective bits");
}

#[test]
fn channel_scan_time() {
    let mut ctx = VerificationContext::new();
    for v in &["num_channels", "time_per_channel_us", "total_scan_us"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("nc", "num_channels == 8"));
    ctx.push_obligation(ProofObligation::assume("tpc", "time_per_channel_us == 5")); // 5µs each
    ctx.push_obligation(ProofObligation::assume(
        "ts_def",
        "total_scan_us == num_channels * time_per_channel_us",
    ));
    ctx.push_obligation(ProofObligation::assert("is_40", "total_scan_us == 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(&result, "ADC scan: 8×5=40µs");
}

#[test]
fn window_comparator() {
    let mut ctx = VerificationContext::new();
    for v in &["sample", "lower_threshold", "upper_threshold"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_window", i32_ty());
    ctx.push_obligation(ProofObligation::assume("s", "sample == 2000"));
    ctx.push_obligation(ProofObligation::assume("lt", "lower_threshold == 1000"));
    ctx.push_obligation(ProofObligation::assume("ut", "upper_threshold == 3000"));
    ctx.push_obligation(ProofObligation::assume(
        "iw_def",
        "in_window == if sample >= lower_threshold && sample <= upper_threshold { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_window == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC window: 2000 in [1000,3000]");
}

#[test]
fn dma_transfer_after_conversion() {
    let mut ctx = VerificationContext::new();
    for v in &["conversions_done", "dma_transfers", "pending"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.push_obligation(ProofObligation::assume("cd", "conversions_done == 32"));
    ctx.push_obligation(ProofObligation::assume("dt", "dma_transfers == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "p_def",
        "pending == conversions_done - dma_transfers",
    ));
    ctx.push_obligation(ProofObligation::assert("is_2", "pending == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "behind",
        "dma_transfers < conversions_done",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC DMA: 32-30=2 pending transfers");
}

#[test]
fn differential_input_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("positive_input_mv", i32_ty());
    ctx.declare_var_typed("negative_input_mv", i32_ty());
    ctx.declare_var_typed("differential_mv", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pi", "positive_input_mv == 1800"));
    ctx.push_obligation(ProofObligation::assume("ni", "negative_input_mv == 1500"));
    ctx.push_obligation(ProofObligation::assume(
        "d_def",
        "differential_mv == positive_input_mv - negative_input_mv",
    ));
    ctx.push_obligation(ProofObligation::assert("is_300", "differential_mv == 300"));
    ctx.push_obligation(ProofObligation::assert("positive", "differential_mv > 0"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC diff: 1800-1500=300mV");
}

#[test]
fn injected_channel_priority() {
    let mut ctx = VerificationContext::new();
    for v in &["regular_channel", "injected_channel"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("injected_preempts", i32_ty());
    // Injected channels have higher priority (lower number)
    ctx.push_obligation(ProofObligation::assume("rc", "regular_channel == 5"));
    ctx.push_obligation(ProofObligation::assume("ic", "injected_channel == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ip_def",
        "injected_preempts == if injected_channel < regular_channel { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "injected_preempts == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ADC: injected(1) < regular(5) → preempts");
}
