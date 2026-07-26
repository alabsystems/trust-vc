// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn scale_factor() {
    let mut ctx = VerificationContext::new();
    for v in &["sf_x1000", "min_sf_x1000", "max_sf_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("sf_ok", i32_ty());
    // Scale factor accuracy (×1000 for 0.001 LSB/°/s)
    ctx.push_obligation(ProofObligation::assume("sx", "sf_x1000 == 1000")); // 1.000
    ctx.push_obligation(ProofObligation::assume("mn", "min_sf_x1000 == 990")); // 0.990
    ctx.push_obligation(ProofObligation::assume("mx", "max_sf_x1000 == 1010")); // 1.010 (±1%)
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "sf_ok == if sf_x1000 >= min_sf_x1000 && sf_x1000 <= max_sf_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "sf_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: scale factor 1.000 in [0.990, 1.010] → OK");
}

#[test]
fn noise_density() {
    let mut ctx = VerificationContext::new();
    for v in &["noise_mdps_per_sqrt_hz", "max_noise"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("noise_ok", i32_ty());
    // Rate noise density: m°/s/√Hz
    ctx.push_obligation(ProofObligation::assume("nm", "noise_mdps_per_sqrt_hz == 4"));
    ctx.push_obligation(ProofObligation::assume("mn", "max_noise == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "noise_ok == if noise_mdps_per_sqrt_hz <= max_noise { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "noise_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 4 m°/s/√Hz noise ≤ 10 max → OK");
}

#[test]
fn bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "min_bw_hz", "max_bw_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Output bandwidth (configurable via digital filter)
    ctx.push_obligation(ProofObligation::assume("bh", "bw_hz == 200"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw_hz == 800"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_hz >= min_bw_hz && bw_hz <= max_bw_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 200Hz bandwidth in [10, 800] → OK");
}

#[test]
fn full_scale_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fsr_dps", u32_ty());
    ctx.declare_var_typed("valid_fsr", i32_ty());
    // Full-scale range: standard settings
    ctx.push_obligation(ProofObligation::assume("fd", "fsr_dps == 2000"));
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_fsr == if fsr_dps == 125 || fsr_dps == 250 || fsr_dps == 500 || fsr_dps == 1000 || fsr_dps == 2000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_fsr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 2000°/s is a valid full-scale range");
}

#[test]
fn bias_instability() {
    let mut ctx = VerificationContext::new();
    for v in &["bias_dph_x10", "max_bias_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bias_ok", i32_ty());
    // In-run bias instability: °/h (×10 for 0.1 resolution)
    ctx.push_obligation(ProofObligation::assume("bx", "bias_dph_x10 == 30")); // 3.0°/h
    ctx.push_obligation(ProofObligation::assume("mb", "max_bias_x10 == 100")); // 10.0°/h
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bias_ok == if bias_dph_x10 <= max_bias_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bias_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 3.0°/h bias instability ≤ 10.0 max → OK");
}

#[test]
fn cross_axis_sensitivity() {
    let mut ctx = VerificationContext::new();
    for v in &["cross_pct_x10", "max_cross_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cross_ok", i32_ty());
    // Cross-axis sensitivity: % (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("cx", "cross_pct_x10 == 10")); // 1.0%
    ctx.push_obligation(ProofObligation::assume("mc", "max_cross_x10 == 30")); // 3.0%
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cross_ok == if cross_pct_x10 <= max_cross_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cross_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 1.0% cross-axis ≤ 3.0% max → OK");
}

#[test]
fn shock_survival() {
    let mut ctx = VerificationContext::new();
    for v in &["shock_g", "max_shock_g"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("shock_ok", i32_ty());
    // Mechanical shock survival rating
    ctx.push_obligation(ProofObligation::assume("sg", "shock_g == 5000"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_shock_g == 10000"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "shock_ok == if shock_g <= max_shock_g { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "shock_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 5000g shock ≤ 10000g survival → OK");
}

#[test]
fn startup_time() {
    let mut ctx = VerificationContext::new();
    for v in &["startup_ms", "max_startup_ms"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("start_ok", i32_ty());
    // Time from power-on to valid data
    ctx.push_obligation(ProofObligation::assume("sm", "startup_ms == 50"));
    ctx.push_obligation(ProofObligation::assume("ms", "max_startup_ms == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "so_def",
        "start_ok == if startup_ms <= max_startup_ms { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "start_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 50ms startup ≤ 200ms max → OK");
}

#[test]
fn digital_filter_odr() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("odr_hz", u32_ty());
    ctx.declare_var_typed("valid_odr", i32_ty());
    // Output Data Rate settings
    ctx.push_obligation(ProofObligation::assume("oh", "odr_hz == 400"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_odr == if odr_hz == 100 || odr_hz == 200 || odr_hz == 400 || odr_hz == 800 || odr_hz == 1600 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_odr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 400Hz is a valid ODR setting");
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_x10", "min_temp_x10", "max_temp_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature (×10, offset +500 for negative)
    ctx.push_obligation(ProofObligation::assume("tx", "temp_x10 == 750")); // 25.0°C
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_x10 == 100")); // -40.0°C
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_x10 == 1350")); // 85.0°C
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_x10 >= min_temp_x10 && temp_x10 <= max_temp_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Gyro: 25°C in [-40, 85] → operating temp OK");
}
