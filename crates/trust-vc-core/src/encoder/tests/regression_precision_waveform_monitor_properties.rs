// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_waveform_monitor_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw", i32_ty());
    ctx.push_obligation(ProofObligation::assume("bw_range", "bw >= 1 && bw <= 5000"));
    ctx.push_obligation(ProofObligation::assert(
        "bw_bounded",
        "bw >= 1 && bw <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth in [1, 5000] MHz");
}

#[test]
fn test_waveform_monitor_input_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ch", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ch_range", "ch >= 1 && ch <= 16"));
    ctx.push_obligation(ProofObligation::assert("ch_bounded", "ch >= 1 && ch <= 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input channels in [1, 16]");
}

#[test]
fn test_waveform_monitor_vertical_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res >= 8 && res <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res >= 8 && res <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vertical resolution in [8, 16] bits");
}

#[test]
fn test_waveform_monitor_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate >= 1 && rate <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "rate >= 1 && rate <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample rate in [1, 50000] MSa/s");
}

#[test]
fn test_waveform_monitor_record_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("len", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "len_range",
        "len >= 1000 && len <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "len_bounded",
        "len >= 1000 && len <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "record length in [1000, 100000000] points");
}

#[test]
fn test_waveform_monitor_dynamic_range_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_x10_range",
        "range_x10 > 0 && range_x10 < 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_x10_bounded",
        "range_x10 > 0 && range_x10 < 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range x10 dB in (0, 1000)");
}

#[test]
fn test_waveform_monitor_display_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_vals",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_bounded",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "display mode is waveform, eye-diagram, or constellation",
    );
}

#[test]
fn test_waveform_monitor_trigger_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "source_vals",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_bounded",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trigger source is internal, external, or pattern");
}

#[test]
fn test_waveform_monitor_analysis_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analysis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "analysis_vals",
        "analysis == 1 || analysis == 2 || analysis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "analysis_bounded",
        "analysis == 1 || analysis == 2 || analysis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis mode is time-domain, frequency-domain, or statistical",
    );
}

#[test]
fn test_waveform_monitor_auto_mask_testing_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mask", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mask_vals",
        "mask == 0 || mask == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mask_bounded",
        "mask == 0 || mask == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic mask testing flag is 0 or 1");
}
