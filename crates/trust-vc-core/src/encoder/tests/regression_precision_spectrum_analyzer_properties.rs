// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: precision spectrum analyzer property verification

use super::*;

#[test]
fn test_frequency_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_ghz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "freq_ghz >= 1 && freq_ghz <= 110",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "freq_ghz == 26"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "freq_ghz >= 1 && freq_ghz <= 110",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency max 26 GHz within 1-110 GHz range");
}

#[test]
fn test_rbw_min_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rbw_hz", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rbw_hz >= 1 && rbw_hz <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rbw_hz == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rbw_hz >= 1 && rbw_hz <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution bandwidth 1 Hz within 1-1000 Hz range");
}

#[test]
fn test_phase_noise_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase_noise_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "phase_noise_x10 >= 50 && phase_noise_x10 <= 250",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "phase_noise_x10 == 106"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "phase_noise_x10 >= 50 && phase_noise_x10 <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "phase noise x10 offset 106 (meaning -94 dBc/Hz at 10kHz) within 50-250 range",
    );
}

#[test]
fn test_danl_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("danl_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "danl_x10 >= 10 && danl_x10 <= 250",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "danl_x10 == 37"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "danl_x10 >= 10 && danl_x10 <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "DANL x10 offset 37 (meaning -163 dBm) within 10-250 range",
    );
}

#[test]
fn test_sweep_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sweep_ghz_per_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sweep_ghz_per_s >= 1 && sweep_ghz_per_s <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "sweep_ghz_per_s == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sweep_ghz_per_s >= 1 && sweep_ghz_per_s <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sweep speed 1000 GHz/s within 1-10000 GHz/s range");
}

#[test]
fn test_dynamic_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dynamic_range_db", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "dynamic_range_db >= 50 && dynamic_range_db <= 150",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "dynamic_range_db == 110"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dynamic_range_db >= 50 && dynamic_range_db <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dynamic range 110 dB within 50-150 dB range");
}

#[test]
fn test_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type is peak(1), RMS(2), or average(3)");
}

#[test]
fn test_window_function_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("window", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "window == 1 || window == 2 || window == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "window == 1 || window == 2 || window == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "window function is Gaussian(1), flat-top(2), or Kaiser(3)",
    );
}

#[test]
fn test_trigger_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trigger", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "trigger == 1 || trigger == 2 || trigger == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "trigger == 1 || trigger == 2 || trigger == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trigger mode is free-run(1), video(2), or external(3)",
    );
}

#[test]
fn test_real_time_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "rt_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "real-time flag set implies conditional evaluates to 1",
    );
}
