// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_cl_spec_wavelength_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_wavelength",
        "wavelength_nm >= 200 && wavelength_nm <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_wavelength",
        "wavelength_nm >= 200 && wavelength_nm <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection wavelength must be in 200-2000 nm range");
}

#[test]
fn test_cl_spec_spectral_resolution_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spectral_resolution_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_resolution",
        "spectral_resolution_x100 >= 1 && spectral_resolution_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_resolution",
        "spectral_resolution_x100 >= 1 && spectral_resolution_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral resolution x100 must be in 1-5000 range (0.01-50.00 nm)",
    );
}

#[test]
fn test_cl_spec_beam_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beam_voltage_kv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_voltage",
        "beam_voltage_kv >= 1 && beam_voltage_kv <= 30",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_voltage",
        "beam_voltage_kv >= 1 && beam_voltage_kv <= 30",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "electron beam voltage must be in 1-30 kV range");
}

#[test]
fn test_cl_spec_beam_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("beam_current_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_current",
        "beam_current_x100 >= 1 && beam_current_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_current",
        "beam_current_x100 >= 1 && beam_current_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "beam current x100 must be in 1-100000 range (0.01-1000.00 nA)",
    );
}

#[test]
fn test_cl_spec_spatial_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spatial_resolution_nm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_spatial",
        "spatial_resolution_nm >= 1 && spatial_resolution_nm <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_spatial",
        "spatial_resolution_nm >= 1 && spatial_resolution_nm <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spatial resolution must be in 1-10000 nm range");
}

#[test]
fn test_cl_spec_detector_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_channels",
        "detector_channels >= 1 && detector_channels <= 2048",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_channels",
        "detector_channels >= 1 && detector_channels <= 2048",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector channels must be in 1-2048 range");
}

#[test]
fn test_cl_spec_detector_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_detector",
        "detector_type >= 1 && detector_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_detector",
        "detector_type >= 1 && detector_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type must be 1=PMT, 2=CCD, or 3=InGaAs-array",
    );
}

#[test]
fn test_cl_spec_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("measurement_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_mode",
        "measurement_mode >= 1 && measurement_mode <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_mode",
        "measurement_mode >= 1 && measurement_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode must be 1=panchromatic, 2=monochromatic, or 3=hyperspectral",
    );
}

#[test]
fn test_cl_spec_cryostage_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cryostage_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_cryostage",
        "cryostage_type >= 1 && cryostage_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_cryostage",
        "cryostage_type >= 1 && cryostage_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cryostage type must be 1=liquid-nitrogen, 2=liquid-helium, or 3=Peltier",
    );
}

#[test]
fn test_cl_spec_auto_beam_blanking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_beam_blanking", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_blanking",
        "auto_beam_blanking >= 0 && auto_beam_blanking <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_blanking",
        "auto_beam_blanking >= 0 && auto_beam_blanking <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto beam blanking flag must be 0=disabled or 1=enabled",
    );
}
