// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ldv_velocity_range_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vr_a",
        "vel_x100 >= 1 && vel_x100 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vr_c",
        "vel_x100 >= 1 && vel_x100 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "velocity range x100 in [1, 1000000] representing 0.01-10000.00 mm/s",
    );
}

#[test]
fn test_ldv_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_hz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fr_a",
        "freq_hz >= 0 && freq_hz <= 25000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fr_c",
        "freq_hz >= 0 && freq_hz <= 25000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency range in [0, 25000000] Hz (0-25 MHz)");
}

#[test]
fn test_ldv_standoff_distance_mm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("standoff_mm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sd_a",
        "standoff_mm >= 10 && standoff_mm <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sd_c",
        "standoff_mm >= 10 && standoff_mm <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "standoff distance in [10, 100000] mm (10mm-100m)");
}

#[test]
fn test_ldv_laser_wavelength_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wl_a",
        "wavelength_nm >= 400 && wavelength_nm <= 1600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wl_c",
        "wavelength_nm >= 400 && wavelength_nm <= 1600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser wavelength in [400, 1600] nm (visible to near-IR)",
    );
}

#[test]
fn test_ldv_displacement_resolution_pm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_pm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dr_a",
        "res_pm >= 1 && res_pm <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dr_c",
        "res_pm >= 1 && res_pm <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "displacement resolution in [1, 100000] pm (sub-picometer to 100nm)",
    );
}

#[test]
fn test_ldv_laser_power_uw_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_uw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lp_a",
        "power_uw >= 10 && power_uw <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lp_c",
        "power_uw >= 10 && power_uw <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser power in [10, 50000] uW");
}

#[test]
fn test_ldv_decoder_type_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("decoder", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "decoder == 1 || decoder == 2 || decoder == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "decoder == 1 || decoder == 2 || decoder == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "decoder: heterodyne, homodyne, or digital demodulation",
    );
}

#[test]
fn test_ldv_scan_head_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scan_head", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sh_a",
        "scan_head == 1 || scan_head == 2 || scan_head == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sh_c",
        "scan_head == 1 || scan_head == 2 || scan_head == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scan head: single-point, scanning mirror, or 3D full-field",
    );
}

#[test]
fn test_ldv_measurement_axis_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_axis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ma_a",
        "meas_axis == 1 || meas_axis == 2 || meas_axis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ma_c",
        "meas_axis == 1 || meas_axis == 2 || meas_axis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement axis: out-of-plane, in-plane, or rotational",
    );
}

#[test]
fn test_ldv_auto_focus_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_focus", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "af_a",
        "auto_focus == 0 || auto_focus == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "af_c",
        "auto_focus == 0 || auto_focus == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-focus flag is boolean");
}
