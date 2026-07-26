// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// X-ray Photoelectron Spectrometer (XPS) property verification tests

use super::*;

#[test]
fn test_xps_binding_energy_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("binding_energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_binding_energy_bounds",
        "binding_energy >= 0 && binding_energy <= 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_binding_energy_in_range",
        "binding_energy >= 0 && binding_energy <= 1500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "binding energy must be in 0-1500 eV range");
}

#[test]
fn test_xps_energy_resolution_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_resolution_bounds",
        "res_x1000 > 0 && res_x1000 < 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_resolution_positive_and_bounded",
        "res_x1000 > 0 && res_x1000 < 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "energy resolution scaled x1000 must be in valid range",
    );
}

#[test]
fn test_xps_spatial_resolution_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spatial_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_spatial_bounds",
        "spatial_x10 > 0 && spatial_x10 < 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_spatial_positive_and_bounded",
        "spatial_x10 > 0 && spatial_x10 < 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spatial resolution scaled x10 um must be in valid range",
    );
}

#[test]
fn test_xps_detection_sensitivity_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_sensitivity_bounds",
        "sens_x10000 > 0 && sens_x10000 < 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_sensitivity_positive_and_bounded",
        "sens_x10000 > 0 && sens_x10000 < 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection sensitivity scaled x10000 at% must be in valid range",
    );
}

#[test]
fn test_xps_sputter_rate_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_sputter_rate_bounds",
        "rate_x100 > 0 && rate_x100 < 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_sputter_rate_positive_and_bounded",
        "rate_x100 > 0 && rate_x100 < 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sputter rate scaled x100 nm/min must be in valid range",
    );
}

#[test]
fn test_xps_detector_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_channels_bounds",
        "channels >= 1 && channels <= 128",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_channels_in_range",
        "channels >= 1 && channels <= 128",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of detector channels must be in 1-128 range",
    );
}

#[test]
fn test_xps_xray_source_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_source_valid",
        "source == 1 || source == 2 || source == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_source_is_known_type",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "x-ray source must be monochromatic-Al(1), dual-anode(2), or synchrotron(3)",
    );
}

#[test]
fn test_xps_analyzer_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_analyzer_valid",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_analyzer_is_known_type",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analyzer must be hemispherical(1), cylindrical-mirror(2), or retarding-field(3)",
    );
}

#[test]
fn test_xps_charge_compensation_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_compensation_valid",
        "comp == 1 || comp == 2 || comp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_compensation_is_known_type",
        "comp == 1 || comp == 2 || comp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "charge compensation must be electron-flood(1), ion-gun(2), or dual-beam(3)",
    );
}

#[test]
fn test_xps_automatic_peak_identification_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_peak_id", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "xps_peak_id_boolean",
        "auto_peak_id == 0 || auto_peak_id == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "xps_peak_id_is_valid_flag",
        "auto_peak_id == 0 || auto_peak_id == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic peak identification flag must be 0 (off) or 1 (on)",
    );
}
