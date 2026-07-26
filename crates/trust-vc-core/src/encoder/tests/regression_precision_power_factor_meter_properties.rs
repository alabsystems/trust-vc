// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_power_factor_meter_voltage_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 50 && voltage <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 50 && voltage <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement voltage must be between 50 and 1000 V");
}

#[test]
fn test_power_factor_meter_current_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current >= 1 && current <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_bounded",
        "current >= 1 && current <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement current must be between 1 and 2000 A");
}

#[test]
fn test_power_factor_meter_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("frequency", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "frequency_range",
        "frequency >= 25 && frequency <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "frequency_bounded",
        "frequency >= 25 && frequency <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency must be between 25 and 1000 Hz");
}

#[test]
fn test_power_factor_meter_power_factor_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pf_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pf_range",
        "pf_x1000 >= 0 && pf_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pf_bounded",
        "pf_x1000 >= 0 && pf_x1000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power factor x1000 must be between 0 and 1000");
}

#[test]
fn test_power_factor_meter_phase_angle_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("phase_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "phase_range",
        "phase_x10 >= 0 && phase_x10 <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "phase_bounded",
        "phase_x10 >= 0 && phase_x10 <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "phase angle x10 must be between 0 and 3600");
}

#[test]
fn test_power_factor_meter_accuracy_class_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_range",
        "accuracy_x100 >= 1 && accuracy_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_bounded",
        "accuracy_x100 >= 1 && accuracy_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy class x100 must be between 1 and 500");
}

#[test]
fn test_power_factor_meter_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_range",
        "mode >= 1 && mode <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement mode must be 1=single-phase, 2=three-phase-balanced, or 3=three-phase-unbalanced");
}

#[test]
fn test_power_factor_meter_display_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("display", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "display_range",
        "display >= 1 && display <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "display_valid",
        "display == 1 || display == 2 || display == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "display type must be 1=analog, 2=digital, or 3=graphical",
    );
}

#[test]
fn test_power_factor_meter_connection_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("connection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "connection_range",
        "connection >= 1 && connection <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "connection_valid",
        "connection == 1 || connection == 2 || connection == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "connection type must be 1=direct, 2=CT-connected, or 3=PT-CT-connected",
    );
}

#[test]
fn test_power_factor_meter_auto_range_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_range_range",
        "auto_range >= 0 && auto_range <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_range_valid",
        "auto_range == 0 || auto_range == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto range flag must be 0=disabled or 1=enabled");
}
