// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_micro_raman_laser_wavelength_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("laser_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lw_a",
        "laser_nm >= 200 && laser_nm <= 1100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lw_c",
        "laser_nm >= 200 && laser_nm <= 1100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "laser wavelength in [200, 1100] nm (UV through NIR)",
    );
}

#[test]
fn test_micro_raman_spectral_resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spec_res_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sr_a",
        "spec_res_x10 >= 1 && spec_res_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sr_c",
        "spec_res_x10 >= 1 && spec_res_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral resolution x10 in [1, 100] representing 0.1-10.0 cm^-1",
    );
}

#[test]
fn test_micro_raman_laser_power_uw_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_uw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lp_a",
        "power_uw >= 1 && power_uw <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lp_c",
        "power_uw >= 1 && power_uw <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser power in [1, 500000] uW (1uW-500mW)");
}

#[test]
fn test_micro_raman_spatial_resolution_nm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spatial_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sp_a",
        "spatial_nm >= 200 && spatial_nm <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sp_c",
        "spatial_nm >= 200 && spatial_nm <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spatial resolution in [200, 10000] nm (diffraction-limited)",
    );
}

#[test]
fn test_micro_raman_spectral_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_cm1", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rg_a",
        "range_cm1 >= 50 && range_cm1 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rg_c",
        "range_cm1 >= 50 && range_cm1 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spectral range in [50, 10000] cm^-1");
}

#[test]
fn test_micro_raman_integration_time_ms_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("int_time_ms", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "it_a",
        "int_time_ms >= 1 && int_time_ms <= 600000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "it_c",
        "int_time_ms >= 1 && int_time_ms <= 600000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "integration time in [1, 600000] ms (1ms-10min)");
}

#[test]
fn test_micro_raman_detector_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector: CCD, EMCCD, or InGaAs");
}

#[test]
fn test_micro_raman_grating_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("grating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gr_a",
        "grating == 1 || grating == 2 || grating == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gr_c",
        "grating == 1 || grating == 2 || grating == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "grating: 600 gr/mm, 1200 gr/mm, or 1800 gr/mm");
}

#[test]
fn test_micro_raman_measurement_mode_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mm_a",
        "meas_mode == 1 || meas_mode == 2 || meas_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mm_c",
        "meas_mode == 1 || meas_mode == 2 || meas_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mode: single point, line scan, or area mapping");
}

#[test]
fn test_micro_raman_confocal_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("confocal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cf_a",
        "confocal == 0 || confocal == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cf_c",
        "confocal == 0 || confocal == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "confocal pinhole flag is boolean");
}
