// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: precision digital phosphor oscilloscope property verification

use super::*;

#[test]
fn test_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "bandwidth_mhz >= 100 && bandwidth_mhz <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "bandwidth_mhz == 4000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "bandwidth_mhz >= 100 && bandwidth_mhz <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth 4000 MHz within 100-20000 MHz range");
}

#[test]
fn test_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate_gsps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sample_rate_gsps >= 1 && sample_rate_gsps <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sample_rate_gsps == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sample_rate_gsps >= 1 && sample_rate_gsps <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample rate 50 GSa/s within 1-100 GSa/s range");
}

#[test]
fn test_record_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("record_length_mpts", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "record_length_mpts >= 1 && record_length_mpts <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "record_length_mpts == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "record_length_mpts >= 1 && record_length_mpts <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "record length 250 million points within 1-500 million points range",
    );
}

#[test]
fn test_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 2 && channels <= 8",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 2 && channels <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "channel count 4 within 2-8 analog input channels range",
    );
}

#[test]
fn test_vertical_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vertical_resolution_bits", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "vertical_resolution_bits >= 8 && vertical_resolution_bits <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "vertical_resolution_bits == 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "vertical_resolution_bits >= 8 && vertical_resolution_bits <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vertical resolution 12 bits within 8-16 bits range",
    );
}

#[test]
fn test_waveform_update_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("update_rate_wfms", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "update_rate_wfms >= 1000 && update_rate_wfms <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "update_rate_wfms == 300000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "update_rate_wfms >= 1000 && update_rate_wfms <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "waveform update rate 300000 wfms/s within 1000-500000 wfms/s range",
    );
}

#[test]
fn test_phosphor_persistence_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("persistence_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "persistence_mode == 1 || persistence_mode == 2 || persistence_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "persistence_mode == 1 || persistence_mode == 2 || persistence_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "phosphor persistence mode is variable(1), infinite(2), or color-graded(3)",
    );
}

#[test]
fn test_trigger_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "trigger_type == 1 || trigger_type == 2 || trigger_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trigger_type == 1 || trigger_type == 2 || trigger_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger type is edge(1), pulse-width(2), or serial-pattern(3)",
    );
}

#[test]
fn test_math_function_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("math_fn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "math_fn == 1 || math_fn == 2 || math_fn == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "math_fn == 1 || math_fn == 2 || math_fn == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "math function is fft(1), arbitrary(2), or spectral(3)",
    );
}

#[test]
fn test_segmented_acquisition_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("enabled", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "segmented",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "segmented acquisition flag enabled implies conditional evaluates to 1",
    );
}
