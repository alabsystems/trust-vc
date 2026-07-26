// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// --- Precision Thermal Imaging Analyzer Properties ---
//
// Formal verification of constraints for an infrared thermal camera system
// used in predictive maintenance and R&D thermal analysis. All parameters
// are modeled as i32 with scaled-integer encoding where fractional values
// are needed (e.g., NETD sensitivity in millikelvins, spectral range in
// tenths of micrometers).

/// Resolution must be between 1,000 and 1,000,000 pixels.
#[test]
fn test_thermal_imaging_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pixels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pixels_range",
        "pixels >= 1000 && pixels <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pixels_bounded",
        "pixels >= 1000 && pixels <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resolution must be between 1000 and 1000000 pixels",
    );
}

/// Frame rate must be between 1 and 1000 Hz.
#[test]
fn test_thermal_imaging_frame_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frame_rate_hz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "frame_rate_range",
        "frame_rate_hz >= 1 && frame_rate_hz <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "frame_rate_bounded",
        "frame_rate_hz >= 1 && frame_rate_hz <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frame rate must be between 1 and 1000 Hz");
}

/// Temperature range span must be between 100 and 3000 degrees Celsius.
#[test]
fn test_thermal_imaging_temperature_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_range_c", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_range_c >= 100 && temp_range_c <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_range_bounded",
        "temp_range_c >= 100 && temp_range_c <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature range must be between 100 and 3000 degrees C",
    );
}

/// Thermal sensitivity (NETD) x1000: range 1-500 representing 0.001-0.500 K.
#[test]
fn test_thermal_imaging_sensitivity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("netd_mk", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "netd_range",
        "netd_mk >= 1 && netd_mk <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "netd_bounded",
        "netd_mk >= 1 && netd_mk <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NETD sensitivity x1000 must be between 1 and 500 millikelvins",
    );
}

/// Spectral range x10: range 10-200 representing 1.0-20.0 micrometers.
#[test]
fn test_thermal_imaging_spectral_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spectral_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spectral_range",
        "spectral_x10 >= 10 && spectral_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spectral_bounded",
        "spectral_x10 >= 10 && spectral_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spectral range x10 must be between 10 and 200 tenths of um",
    );
}

/// Number of measurement spots must be between 1 and 128.
#[test]
fn test_thermal_imaging_measurement_spots_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spots", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spots_range",
        "spots >= 1 && spots <= 128",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spots_bounded",
        "spots >= 1 && spots <= 128",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement spots must be between 1 and 128");
}

/// Detector type is a 3-way disjunction: 1=microbolometer, 2=InSb, 3=MCT.
#[test]
fn test_thermal_imaging_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_valid",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_disjunction",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector type must be microbolometer(1), InSb(2), or MCT(3)",
    );
}

/// Measurement mode is a 3-way disjunction: 1=spot, 2=area, 3=line-profile.
#[test]
fn test_thermal_imaging_measurement_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "meas_mode == 1 || meas_mode == 2 || meas_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_disjunction",
        "meas_mode == 1 || meas_mode == 2 || meas_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode must be spot(1), area(2), or line-profile(3)",
    );
}

/// Output format is a 3-way disjunction: 1=radiometric, 2=visual, 3=fusion.
#[test]
fn test_thermal_imaging_output_format_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_fmt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "format_valid",
        "output_fmt == 1 || output_fmt == 2 || output_fmt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "format_disjunction",
        "output_fmt == 1 || output_fmt == 2 || output_fmt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "output format must be radiometric(1), visual(2), or fusion(3)",
    );
}

/// Automatic emissivity correction is a boolean flag (0 or 1).
#[test]
fn test_thermal_imaging_emissivity_correction_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_emissivity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "emissivity_bool",
        "auto_emissivity == 0 || auto_emissivity == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "emissivity_flag",
        "auto_emissivity == 0 || auto_emissivity == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "emissivity correction flag must be 0 (off) or 1 (on)",
    );
}
