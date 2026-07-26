// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_portable_xrf_tube_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 5 && voltage <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 5 && voltage <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube voltage must be between 5 and 50 kV");
}

#[test]
fn test_portable_xrf_measurement_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_range",
        "meas_time >= 1 && meas_time <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_bounded",
        "meas_time >= 1 && meas_time <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement time must be between 1 and 300 seconds",
    );
}

#[test]
fn test_portable_xrf_detection_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_limit_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_limit_range",
        "det_limit_x100 >= 1 && det_limit_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_limit_bounded",
        "det_limit_x100 >= 1 && det_limit_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit x100 must be in range 1-50000 representing 0.01-500.00 ppm",
    );
}

#[test]
fn test_portable_xrf_battery_life_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("battery_hours", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "battery_range",
        "battery_hours >= 1 && battery_hours <= 24",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "battery_bounded",
        "battery_hours >= 1 && battery_hours <= 24",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "battery life must be between 1 and 24 hours");
}

#[test]
fn test_portable_xrf_weight_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("weight_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "weight_range",
        "weight_x10 >= 5 && weight_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "weight_bounded",
        "weight_x10 >= 5 && weight_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "weight x10 must be in range 5-50 representing 0.5-5.0 kg",
    );
}

#[test]
fn test_portable_xrf_stored_spectra_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spectra_count", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spectra_range",
        "spectra_count >= 1 && spectra_count <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spectra_bounded",
        "spectra_count >= 1 && spectra_count <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stored spectra count must be between 1 and 100000");
}

#[test]
fn test_portable_xrf_application_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("app_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "app_mode_valid",
        "app_mode == 1 || app_mode == 2 || app_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "app_mode_disjunction",
        "app_mode == 1 || app_mode == 2 || app_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "application mode must be 1=alloy-sorting, 2=mining-exploration, or 3=environmental",
    );
}

#[test]
fn test_portable_xrf_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_disjunction",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type must be 1=SDD, 2=Si-PIN, or 3=CdTe");
}

#[test]
fn test_portable_xrf_calibration_method_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cal_method_valid",
        "cal_method == 1 || cal_method == 2 || cal_method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cal_method_disjunction",
        "cal_method == 1 || cal_method == 2 || cal_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "calibration method must be 1=fundamental-parameters, 2=empirical, or 3=Compton-normalization",
    );
}

#[test]
fn test_portable_xrf_safety_shutter_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shutter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shutter_bool",
        "shutter == 0 || shutter == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shutter_is_boolean",
        "shutter == 0 || shutter == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic safety shutter flag must be boolean (0 or 1)",
    );
}
