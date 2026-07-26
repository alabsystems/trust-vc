// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Regression tests: precision time interval analyzer property verification

use super::*;

#[test]
fn test_tia_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x1000ps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "resolution_x1000ps >= 1 && resolution_x1000ps <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "resolution_x1000ps == 20"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "resolution_x1000ps >= 1 && resolution_x1000ps <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resolution x1000 ps value 20 (meaning 0.020 ps) within 1-10000 range",
    );
}

#[test]
fn test_tia_measurement_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_decade_code", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "range_decade_code >= 1 && range_decade_code <= 10",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "range_decade_code == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "range_decade_code >= 1 && range_decade_code <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement range decade code 6 within 1-10 range");
}

#[test]
fn test_tia_single_shot_rms_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rms_x100ps", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rms_x100ps >= 1 && rms_x100ps <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rms_x100ps == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rms_x100ps >= 1 && rms_x100ps <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "single-shot RMS x100 ps value 5 (meaning 0.05 ps) within 1-10000 range",
    );
}

#[test]
fn test_tia_max_input_frequency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "freq_mhz >= 1 && freq_mhz <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "freq_mhz == 12000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "freq_mhz >= 1 && freq_mhz <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "maximum input frequency 12000 MHz within 1-50000 MHz range",
    );
}

#[test]
fn test_tia_number_of_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "channels >= 1 && channels <= 12",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "channels == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "channels >= 1 && channels <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels 4 within 1-12 range");
}

#[test]
fn test_tia_memory_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("memory_depth_k", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "memory_depth_k >= 1 && memory_depth_k <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "memory_depth_k == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "memory_depth_k >= 1 && memory_depth_k <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "memory depth 10000 thousand measurements within 1-100000 range",
    );
}

#[test]
fn test_tia_trigger_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "trigger_mode == 1 || trigger_mode == 2 || trigger_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "trigger_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trigger_mode == 1 || trigger_mode == 2 || trigger_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trigger mode is edge(1), level(2), or pattern(3)");
}

#[test]
fn test_tia_interpolation_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interp_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "interp_method == 1 || interp_method == 2 || interp_method == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "interp_method == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "interp_method == 1 || interp_method == 2 || interp_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "interpolation method is linear(1), vernier(2), or noise-shaping(3)",
    );
}

#[test]
fn test_tia_time_base_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_base", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "time_base == 1 || time_base == 2 || time_base == 3",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "time_base == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "time_base == 1 || time_base == 2 || time_base == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "time base is TCXO(1), OCXO(2), or rubidium(3)");
}

#[test]
fn test_tia_automatic_arming_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "arming_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic arming flag set implies conditional evaluates to 1",
    );
}
