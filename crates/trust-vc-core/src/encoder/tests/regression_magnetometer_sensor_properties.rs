// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn field_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_gauss", u32_ty());
    ctx.declare_var_typed("valid_range", i32_ty());
    // Measurement range in gauss: standard settings
    ctx.push_obligation(ProofObligation::assume("rg", "range_gauss == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vr_def",
        "valid_range == if range_gauss == 2 || range_gauss == 4 || range_gauss == 8 || range_gauss == 16 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: ±4 gauss is a valid range");
}

#[test]
fn resolution() {
    let mut ctx = VerificationContext::new();
    for v in &["res_mgauss", "max_res_mgauss"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("res_ok", i32_ty());
    // Resolution in milligauss (lower = better)
    ctx.push_obligation(ProofObligation::assume("rm", "res_mgauss == 1"));
    ctx.push_obligation(ProofObligation::assume("mr", "max_res_mgauss == 10"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "res_ok == if res_mgauss <= max_res_mgauss { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "res_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: 1 mgauss resolution ≤ 10 max → OK");
}

#[test]
fn noise_density() {
    let mut ctx = VerificationContext::new();
    for v in &["noise_ugauss_per_sqrt_hz", "max_noise"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("noise_ok", i32_ty());
    // Noise density: μgauss/√Hz
    ctx.push_obligation(ProofObligation::assume(
        "nu",
        "noise_ugauss_per_sqrt_hz == 100",
    ));
    ctx.push_obligation(ProofObligation::assume("mn", "max_noise == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "no_def",
        "noise_ok == if noise_ugauss_per_sqrt_hz <= max_noise { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "noise_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: 100μgauss/√Hz noise ≤ 500 max → OK");
}

#[test]
fn mag_bandwidth() {
    let mut ctx = VerificationContext::new();
    for v in &["bw_hz", "min_bw_hz", "max_bw_hz"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("bw_ok", i32_ty());
    // Output bandwidth
    ctx.push_obligation(ProofObligation::assume("bh", "bw_hz == 100"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_bw_hz == 10"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_bw_hz == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "bo_def",
        "bw_ok == if bw_hz >= min_bw_hz && bw_hz <= max_bw_hz { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "bw_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: 100Hz bandwidth in [10, 1000] → OK");
}

#[test]
fn offset_field() {
    let mut ctx = VerificationContext::new();
    for v in &["offset_mgauss", "max_offset_mgauss"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("off_ok", i32_ty());
    // Zero-field offset in milligauss
    ctx.push_obligation(ProofObligation::assume("om", "offset_mgauss == 10"));
    ctx.push_obligation(ProofObligation::assume("mo", "max_offset_mgauss == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "oo_def",
        "off_ok == if offset_mgauss <= max_offset_mgauss { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "off_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: 10 mgauss offset ≤ 50 max → OK");
}

#[test]
fn temperature_coefficient() {
    let mut ctx = VerificationContext::new();
    for v in &["tempco_ppm_per_c", "max_tempco"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("tc_ok", i32_ty());
    // Temperature coefficient: ppm/°C
    ctx.push_obligation(ProofObligation::assume("tp", "tempco_ppm_per_c == 300"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_tempco == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "tc_ok == if tempco_ppm_per_c <= max_tempco { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "tc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: 300ppm/°C tempco ≤ 1000 max → OK");
}

#[test]
fn cross_axis_rejection() {
    let mut ctx = VerificationContext::new();
    for v in &["cross_pct_x10", "max_cross_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cross_ok", i32_ty());
    // Cross-axis sensitivity: % (×10 for 0.1%)
    ctx.push_obligation(ProofObligation::assume("cx", "cross_pct_x10 == 5")); // 0.5%
    ctx.push_obligation(ProofObligation::assume("mc", "max_cross_x10 == 20")); // 2.0%
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cross_ok == if cross_pct_x10 <= max_cross_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cross_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: 0.5% cross-axis ≤ 2.0% max → OK");
}

#[test]
fn sampling_rate() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("odr_hz", u32_ty());
    ctx.declare_var_typed("valid_odr", i32_ty());
    // Output data rate settings
    ctx.push_obligation(ProofObligation::assume("oh", "odr_hz == 100"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_odr == if odr_hz == 10 || odr_hz == 20 || odr_hz == 50 || odr_hz == 100 || odr_hz == 200 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_odr == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: 100Hz is a valid ODR setting");
}

#[test]
fn calibration_diagonal() {
    let mut ctx = VerificationContext::new();
    for v in &["diag_x1000", "min_diag_x1000", "max_diag_x1000"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cal_ok", i32_ty());
    // Calibration matrix diagonal element (×1000, ideal = 1.000)
    ctx.push_obligation(ProofObligation::assume("dx", "diag_x1000 == 998")); // 0.998
    ctx.push_obligation(ProofObligation::assume("mn", "min_diag_x1000 == 950")); // 0.950
    ctx.push_obligation(ProofObligation::assume("mx", "max_diag_x1000 == 1050")); // 1.050
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cal_ok == if diag_x1000 >= min_diag_x1000 && diag_x1000 <= max_diag_x1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Magnetometer: cal diagonal 0.998 in [0.950, 1.050] → OK",
    );
}

#[test]
fn interference_rejection() {
    let mut ctx = VerificationContext::new();
    for v in &["rejection_db", "min_rejection_db"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("rej_ok", i32_ty());
    // Magnetic interference rejection (higher = better)
    ctx.push_obligation(ProofObligation::assume("rd", "rejection_db == 40"));
    ctx.push_obligation(ProofObligation::assume("mr", "min_rejection_db == 20"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "rej_ok == if rejection_db >= min_rejection_db { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "rej_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Magnetometer: 40dB rejection ≥ 20dB min → OK");
}
