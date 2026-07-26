// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_partial_discharge_analyzer_sensitivity_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sens_range",
        "sens_x100 >= 1 && sens_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sens_bounded",
        "sens_x100 >= 1 && sens_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensitivity x100 must be in range 1-100000 representing 0.01-1000.00 pC",
    );
}

#[test]
fn test_partial_discharge_analyzer_bandwidth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bandwidth", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bw_range",
        "bandwidth >= 100 && bandwidth <= 2000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bw_bounded",
        "bandwidth >= 100 && bandwidth <= 2000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bandwidth must be between 100 and 2000000 Hz");
}

#[test]
fn test_partial_discharge_analyzer_test_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 1 && voltage <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 1 && voltage <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage must be between 1 and 500 kV");
}

#[test]
fn test_partial_discharge_analyzer_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chan", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "chan_range",
        "chan >= 1 && chan <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "chan_bounded",
        "chan >= 1 && chan <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "number of measurement channels must be between 1 and 16",
    );
}

#[test]
fn test_partial_discharge_analyzer_noise_floor_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "noise_range",
        "noise_x10 >= 1 && noise_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "noise_bounded",
        "noise_x10 >= 1 && noise_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "noise floor x10 must be in range 1-1000 representing 0.1-100.0 pC",
    );
}

#[test]
fn test_partial_discharge_analyzer_sample_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sample_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sr_range",
        "sample_rate >= 1000 && sample_rate <= 200000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sr_bounded",
        "sample_rate >= 1000 && sample_rate <= 200000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample rate must be between 1000 and 200000000 samples/s",
    );
}

#[test]
fn test_partial_discharge_analyzer_detection_method_three_way() {
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
fn test_partial_discharge_analyzer_display_mode_three_way() {
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
        "display mode must be PRPD (1), 3DPRD (2), or trend (3)",
    );
}

#[test]
fn test_partial_discharge_analyzer_coupling_device_three_way() {
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
        "coupling device must be capacitive (1), HFCT (2), or antenna (3)",
    );
}

#[test]
fn test_partial_discharge_analyzer_auto_noise_gating_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gating", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gating_range",
        "gating == 0 || gating == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gating_valid",
        "gating == 0 || gating == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic noise gating flag must be 0 (disabled) or 1 (enabled)",
    );
}
