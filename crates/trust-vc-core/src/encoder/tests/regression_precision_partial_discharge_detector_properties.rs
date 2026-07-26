// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_partial_discharge_detector_voltage_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volt_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "volt_range",
        "volt_x10 >= 1 && volt_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "volt_bounded",
        "volt_x10 >= 1 && volt_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "voltage x10 must be in range 1-5000 representing 0.1-500.0 kV",
    );
}

#[test]
fn test_partial_discharge_detector_magnitude_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mag_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mag_range",
        "mag_x10 >= 1 && mag_x10 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mag_bounded",
        "mag_x10 >= 1 && mag_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "PD magnitude x10 must be in range 1-100000 representing 0.1-10000.0 pC",
    );
}

#[test]
fn test_partial_discharge_detector_repetition_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate >= 1 && rate <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "rate >= 1 && rate <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "repetition rate must be between 1 and 100000 Hz");
}

#[test]
fn test_partial_discharge_detector_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sens_range",
        "sens_x100 >= 1 && sens_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sens_bounded",
        "sens_x100 >= 1 && sens_x100 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensitivity x100 must be in range 1-1000 representing 0.01-10.00 pC",
    );
}

#[test]
fn test_partial_discharge_detector_bandwidth_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bw_range",
        "bw_x10 >= 1 && bw_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bw_bounded",
        "bw_x10 >= 1 && bw_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "frequency bandwidth x10 must be in range 1-10000 representing 0.1-1000.0 kHz",
    );
}

#[test]
fn test_partial_discharge_detector_noise_floor_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "noise_range",
        "noise_x1000 >= 1 && noise_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "noise_bounded",
        "noise_x1000 >= 1 && noise_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "noise floor x1000 must be in range 1-1000 representing 0.001-1.000 pC",
    );
}

#[test]
fn test_partial_discharge_detector_detection_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "method_range",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "method_valid",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection method must be electrical (1), acoustic (2), or UHF (3)",
    );
}

#[test]
fn test_partial_discharge_detector_coupling_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("coupling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "coupling_range",
        "coupling == 1 || coupling == 2 || coupling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "coupling_valid",
        "coupling == 1 || coupling == 2 || coupling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "coupling mode must be capacitive (1), inductive (2), or directional (3)",
    );
}

#[test]
fn test_partial_discharge_detector_display_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("display", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "display_range",
        "display == 1 || display == 2 || display == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "display_valid",
        "display == 1 || display == 2 || display == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "display mode must be PRPD (1), pulse-train (2), or spectrum (3)",
    );
}

#[test]
fn test_partial_discharge_detector_auto_calibration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto calibration flag must be 0 (disabled) or 1 (enabled)",
    );
}
