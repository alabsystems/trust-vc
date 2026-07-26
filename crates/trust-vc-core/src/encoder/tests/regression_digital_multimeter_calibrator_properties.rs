// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_multimeter_calibrator_dc_voltage_range_bounded() {
    // DC voltage range in millivolts: 1 mV to 1100000 mV (1100 V)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_mv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage_mv >= 1 && voltage_mv <= 1100000",
    ));
    ctx.push_obligation(ProofObligation::assert("lower_bound", "voltage_mv >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "upper_bound",
        "voltage_mv <= 1100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC voltage range: 1 mV to 1100000 mV");
}

#[test]
fn test_multimeter_calibrator_dc_current_range_scaled() {
    // DC current range scaled at x100 microamps (0.01 uA resolution)
    // Range: 1 to 1000000 (represents 0.01 uA to 10000.00 uA = 10 A)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current_x100ua", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current_x100ua >= 1 && current_x100ua <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert("positive", "current_x100ua >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "current_x100ua <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "DC current range x100 uA: 1 to 1000000");
}

#[test]
fn test_multimeter_calibrator_resistance_range_bounded() {
    // Resistance range in ohms: 1 ohm to 100 megaohms
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resistance_ohm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resistance_range",
        "resistance_ohm >= 1 && resistance_ohm <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lower_bound",
        "resistance_ohm >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "upper_bound",
        "resistance_ohm <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resistance range: 1 ohm to 100 Mohm");
}

#[test]
fn test_multimeter_calibrator_accuracy_scaled() {
    // Accuracy scaled at x10000 percent (0.0001% resolution)
    // Range: 1 to 10000 (represents 0.0001% to 1.0000%)
    // Example: 50 = 0.0050%
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_range",
        "accuracy_x10000 >= 1 && accuracy_x10000 <= 10000",
    ));
    // Verify a typical calibrator accuracy of 50 (0.0050%) is within range
    ctx.push_obligation(ProofObligation::assert("positive", "accuracy_x10000 >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "accuracy_x10000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x10000 pct: 1 to 10000 (0.0001% to 1.0000%)",
    );
}

#[test]
fn test_multimeter_calibrator_display_digits_bounded() {
    // Display digits: 4.5 to 8.5 digit meters, encoded as integer 4 to 8
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("digits", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "digits_range",
        "digits >= 4 && digits <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_4", "digits >= 4"));
    ctx.push_obligation(ProofObligation::assert("at_most_8", "digits <= 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "display digits: 4 to 8");
}

#[test]
fn test_multimeter_calibrator_measurement_function_disjunction() {
    // Measurement function: 1=DCV, 2=ACV, 3=resistance
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("meas_func", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_func",
        "meas_func == 1 || meas_func == 2 || meas_func == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_1", "meas_func >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_3", "meas_func <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement function: DCV=1, ACV=2, resistance=3");
}

#[test]
fn test_multimeter_calibrator_input_impedance_disjunction() {
    // Input impedance: 1=10 Mohm, 2=1 Gohm, 3=10 Gohm
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impedance", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_impedance",
        "impedance == 1 || impedance == 2 || impedance == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("at_least_1", "impedance >= 1"));
    ctx.push_obligation(ProofObligation::assert("at_most_3", "impedance <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "input impedance: 10M=1, 1G=2, 10G=3");
}

#[test]
fn test_multimeter_calibrator_calibration_interval_bounded() {
    // Calibration interval in months: 6 to 24
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal_interval_months", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "interval_range",
        "cal_interval_months >= 6 && cal_interval_months <= 24",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_least_6",
        "cal_interval_months >= 6",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_most_24",
        "cal_interval_months <= 24",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "calibration interval: 6 to 24 months");
}

#[test]
fn test_multimeter_calibrator_temperature_coefficient_scaled() {
    // Temperature coefficient scaled at x1000 ppm/degC (0.001 ppm/degC resolution)
    // Range: 1 to 5000 (represents 0.001 to 5.000 ppm/degC)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tempco_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tempco_range",
        "tempco_x1000 >= 1 && tempco_x1000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("positive", "tempco_x1000 >= 1"));
    ctx.push_obligation(ProofObligation::assert("bounded", "tempco_x1000 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temp coefficient x1000 ppm/C: 1 to 5000");
}

#[test]
fn test_multimeter_calibrator_auto_ranging_boolean_flag() {
    // Auto-ranging: boolean flag encoded as i32 (1=enabled, 0=disabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_range", i32_ty());
    ctx.declare_var_typed("enabled", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_range == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "enabled_def",
        "enabled == if auto_range == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("is_enabled", "enabled == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-ranging: flag=1 means enabled");
}
