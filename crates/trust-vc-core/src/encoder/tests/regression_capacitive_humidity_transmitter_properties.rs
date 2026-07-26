// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn measurement_range() {
    let mut ctx = VerificationContext::new();
    for v in &["rh_x10", "max_rh_x10"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("in_range", i32_ty());
    // Relative humidity ×10: 0-100% → 0-1000. Value 650 = 65.0% RH
    ctx.push_obligation(ProofObligation::assume("rx", "rh_x10 == 650"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_rh_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if rh_x10 <= max_rh_x10 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: 65.0% RH in [0, 100] → in range",
    );
}

#[test]
fn accuracy() {
    let mut ctx = VerificationContext::new();
    for v in &["accuracy_x100", "max_accuracy_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("acc_ok", i32_ty());
    // Accuracy ×100: value 200 = 2.00% RH, max 500 = 5.00% RH
    ctx.push_obligation(ProofObligation::assume("ax", "accuracy_x100 == 200"));
    ctx.push_obligation(ProofObligation::assume("ma", "max_accuracy_x100 == 500"));
    ctx.push_obligation(ProofObligation::assume(
        "ao_def",
        "acc_ok == if accuracy_x100 <= max_accuracy_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "acc_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: 2.00% accuracy ≤ 5.00% max → OK",
    );
}

#[test]
fn sensor_element() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("element_type", u32_ty());
    ctx.declare_var_typed("valid_element", i32_ty());
    // Sensor element: 1=polymer capacitive, 2=ceramic capacitive, 3=resistive, 4=thermal conductivity
    ctx.push_obligation(ProofObligation::assume("et", "element_type == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ve_def",
        "valid_element == if element_type == 1 || element_type == 2 || element_type == 3 || element_type == 4 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_element == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: polymer capacitive is valid element type",
    );
}

#[test]
fn response_time() {
    let mut ctx = VerificationContext::new();
    for v in &["t63_sec", "max_t63_sec"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("resp_ok", i32_ty());
    // T63 response time in seconds: value 8s, max 30s
    ctx.push_obligation(ProofObligation::assume("ts", "t63_sec == 8"));
    ctx.push_obligation(ProofObligation::assume("mt", "max_t63_sec == 30"));
    ctx.push_obligation(ProofObligation::assume(
        "ro_def",
        "resp_ok == if t63_sec <= max_t63_sec { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "resp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: 8s T63 response ≤ 30s max → OK",
    );
}

#[test]
fn operating_temperature() {
    let mut ctx = VerificationContext::new();
    for v in &["temp_offset", "min_temp_offset", "max_temp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("temp_ok", i32_ty());
    // Operating temperature offset +500: -40°C=460, 20°C=520, 80°C=580
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_temp_offset == 460"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_temp_offset == 580"));
    ctx.push_obligation(ProofObligation::assume(
        "to_def",
        "temp_ok == if temp_offset >= min_temp_offset && temp_offset <= max_temp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "temp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: 20°C in [-40, 80] → in operating range",
    );
}

#[test]
fn output_signal() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.declare_var_typed("valid_output", i32_ty());
    // Output: 1=4-20mA, 2=0-10V, 3=0-5V, 4=RS485 Modbus, 5=HART
    ctx.push_obligation(ProofObligation::assume("ot", "output_type == 4"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "valid_output == if output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4 || output_type == 5 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "valid_output == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: RS485 Modbus is valid output signal",
    );
}

#[test]
fn hysteresis() {
    let mut ctx = VerificationContext::new();
    for v in &["hyst_x100", "max_hyst_x100"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("hyst_ok", i32_ty());
    // Hysteresis ×100: value 100 = 1.00%, max 200 = 2.00%
    ctx.push_obligation(ProofObligation::assume("hx", "hyst_x100 == 100"));
    ctx.push_obligation(ProofObligation::assume("mh", "max_hyst_x100 == 200"));
    ctx.push_obligation(ProofObligation::assume(
        "ho_def",
        "hyst_ok == if hyst_x100 <= max_hyst_x100 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "hyst_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: 1.00% hysteresis ≤ 2.00% max → OK",
    );
}

#[test]
fn dew_point_range() {
    let mut ctx = VerificationContext::new();
    for v in &["dp_offset", "min_dp_offset", "max_dp_offset"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("dp_ok", i32_ty());
    // Dew point temperature offset +500: -60°C=440, 10°C=510, 100°C=600
    ctx.push_obligation(ProofObligation::assume("do", "dp_offset == 510"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_dp_offset == 440"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_dp_offset == 600"));
    ctx.push_obligation(ProofObligation::assume(
        "do_def",
        "dp_ok == if dp_offset >= min_dp_offset && dp_offset <= max_dp_offset { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "dp_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: 10°C dew point in [-60, 100] → in range",
    );
}

#[test]
fn supply_voltage() {
    let mut ctx = VerificationContext::new();
    for v in &["voltage_mv", "min_voltage_mv", "max_voltage_mv"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("volt_ok", i32_ty());
    // Supply voltage in mV: 24V=24000, min 10V=10000, max 36V=36000
    ctx.push_obligation(ProofObligation::assume("vm", "voltage_mv == 24000"));
    ctx.push_obligation(ProofObligation::assume("mn", "min_voltage_mv == 10000"));
    ctx.push_obligation(ProofObligation::assume("mx", "max_voltage_mv == 36000"));
    ctx.push_obligation(ProofObligation::assume(
        "vo_def",
        "volt_ok == if voltage_mv >= min_voltage_mv && voltage_mv <= max_voltage_mv { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "volt_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Capacitive humidity: 24V supply in [10, 36] → OK");
}

#[test]
fn calibration_interval() {
    let mut ctx = VerificationContext::new();
    for v in &["cal_months", "min_cal_months"] {
        ctx.declare_var_typed(v, u32_ty());
    }
    ctx.declare_var_typed("cal_ok", i32_ty());
    // Calibration interval in months: value 12, min 6
    ctx.push_obligation(ProofObligation::assume("cm", "cal_months == 12"));
    ctx.push_obligation(ProofObligation::assume("mc", "min_cal_months == 6"));
    ctx.push_obligation(ProofObligation::assume(
        "co_def",
        "cal_ok == if cal_months >= min_cal_months { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "cal_ok == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Capacitive humidity: 12-month cal interval ≥ 6-month min → OK",
    );
}
