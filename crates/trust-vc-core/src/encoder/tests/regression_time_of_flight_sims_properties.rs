// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: Time-of-Flight Secondary Ion Mass Spectrometry (TOF-SIMS) instrument properties

use super::*;

#[test]
fn test_tof_sims_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_amu", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_range",
        "mass_amu >= 1 && mass_amu <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_range_valid",
        "mass_amu >= 1 && mass_amu <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS mass range must be bounded between 1 and 10000 amu",
    );
}

#[test]
fn test_tof_sims_mass_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution >= 100 && resolution <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_valid",
        "resolution >= 100 && resolution <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS mass resolution (m/delta-m) must be bounded between 100 and 50000",
    );
}

#[test]
fn test_tof_sims_lateral_resolution_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lat_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lat_range",
        "lat_x10 > 0 && lat_x10 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lat_positive",
        "lat_x10 > 0 && lat_x10 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS lateral resolution scaled x10 nm must be positive and bounded",
    );
}

#[test]
fn test_tof_sims_depth_resolution_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "depth_range",
        "depth_x100 > 0 && depth_x100 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "depth_positive",
        "depth_x100 > 0 && depth_x100 < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS depth resolution scaled x100 nm must be positive and bounded",
    );
}

#[test]
fn test_tof_sims_detection_sensitivity_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x1000", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sens_range",
        "sens_x1000 > 0 && sens_x1000 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sens_positive",
        "sens_x1000 > 0 && sens_x1000 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS detection sensitivity scaled x1000 ppm must be positive and bounded",
    );
}

#[test]
fn test_tof_sims_detector_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "channels_range",
        "channels >= 1 && channels <= 256",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "channels_valid",
        "channels >= 1 && channels <= 256",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS number of detector channels must be between 1 and 256",
    );
}

#[test]
fn test_tof_sims_primary_ion_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "source_known",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS primary ion source must be bismuth(1), cesium(2), or gallium(3)",
    );
}

#[test]
fn test_tof_sims_analysis_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_known",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS analysis mode must be static(1), dynamic(2), or imaging(3)",
    );
}

#[test]
fn test_tof_sims_charge_compensation_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "comp_valid",
        "comp == 1 || comp == 2 || comp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "comp_known",
        "comp == 1 || comp == 2 || comp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS charge compensation must be electron-flood(1), pulsed-electron(2), or none(3)",
    );
}

#[test]
fn test_tof_sims_auto_mass_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_cal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cal_flag",
        "auto_cal == 0 || auto_cal == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cal_boolean",
        "auto_cal == 0 || auto_cal == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "TOF-SIMS automatic mass calibration flag must be boolean (0 or 1)",
    );
}
