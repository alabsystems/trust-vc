// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_power_spectrum_analyzer_freq_span_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("span_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fs_a",
        "span_x10 >= 1 && span_x10 <= 500000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fs_c",
        "span_x10 >= 1 && span_x10 <= 500000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power spectrum analyzer frequency span x10 bounded",
    );
}

#[test]
fn test_power_spectrum_analyzer_resolution_bandwidth_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rbw_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rb_a",
        "rbw_x100 >= 1 && rbw_x100 <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rb_c",
        "rbw_x100 >= 1 && rbw_x100 <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power spectrum analyzer resolution bandwidth x100 bounded",
    );
}

#[test]
fn test_power_spectrum_analyzer_dynamic_range_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drange_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dr_a",
        "drange_x10 >= 500 && drange_x10 <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dr_c",
        "drange_x10 >= 500 && drange_x10 <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power spectrum analyzer dynamic range x10 bounded");
}

#[test]
fn test_power_spectrum_analyzer_noise_floor_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nf_a",
        "noise_off >= 300 && noise_off <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nf_c",
        "noise_off >= 300 && noise_off <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power spectrum analyzer noise floor offset+500 bounded",
    );
}

#[test]
fn test_power_spectrum_analyzer_input_atten_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atten_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ia_a",
        "atten_x10 >= 0 && atten_x10 <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ia_c",
        "atten_x10 >= 0 && atten_x10 <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power spectrum analyzer input attenuation x10 bounded",
    );
}

#[test]
fn test_power_spectrum_analyzer_fft_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fft_size", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ff_a",
        "fft_size >= 64 && fft_size <= 1048576",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ff_c",
        "fft_size >= 64 && fft_size <= 1048576",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power spectrum analyzer FFT size bounded");
}

#[test]
fn test_power_spectrum_analyzer_window_function_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("window_fn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wf_a",
        "window_fn == 1 || window_fn == 2 || window_fn == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wf_c",
        "window_fn == 1 || window_fn == 2 || window_fn == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power spectrum analyzer window function three-way disjunction",
    );
}

#[test]
fn test_power_spectrum_analyzer_averaging_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("avg_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "am_a",
        "avg_mode == 1 || avg_mode == 2 || avg_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "am_c",
        "avg_mode == 1 || avg_mode == 2 || avg_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power spectrum analyzer averaging mode three-way disjunction",
    );
}

#[test]
fn test_power_spectrum_analyzer_trigger_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trig_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ts_a",
        "trig_src == 1 || trig_src == 2 || trig_src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ts_c",
        "trig_src == 1 || trig_src == 2 || trig_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "power spectrum analyzer trigger source three-way disjunction",
    );
}

#[test]
fn test_power_spectrum_analyzer_auto_range_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ar_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ar_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power spectrum analyzer auto range flag");
}
