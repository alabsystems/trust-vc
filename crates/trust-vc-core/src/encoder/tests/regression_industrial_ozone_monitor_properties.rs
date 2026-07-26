// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial ozone monitor property verification.
// Encodes key parameters of an industrial ozone monitoring instrument and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Measurement range (ppb) — bounded [1, 10000], value 1000.
#[test]
fn test_measurement_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_ppb", u32_ty());
    ctx.push_obligation(ProofObligation::assume("range_val", "range_ppb == 1000"));
    ctx.push_obligation(ProofObligation::assert("range_min", "range_ppb >= 1"));
    ctx.push_obligation(ProofObligation::assert("range_max", "range_ppb <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement range 1000 ppb in [1, 10000]");
}

/// Test 2: Detection limit (ppb) — bounded [1, 100], value 5.
#[test]
fn test_detection_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_limit", u32_ty());
    ctx.push_obligation(ProofObligation::assume("det_val", "det_limit == 5"));
    ctx.push_obligation(ProofObligation::assert("det_min", "det_limit >= 1"));
    ctx.push_obligation(ProofObligation::assert("det_max", "det_limit <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection limit 5 ppb in [1, 100]");
}

/// Test 3: Accuracy (×10 % of reading) — bounded [5, 50], value 10 (1.0%).
#[test]
fn test_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "accuracy_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert("acc_min", "accuracy_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("acc_max", "accuracy_x10 <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 1.0% (10 x10) in [5, 50]");
}

/// Test 4: Sensor type — 3-way disjunction.
/// 1=UV absorption, 2=electrochemical, 3=chemiluminescent. Value 1 (UV absorption).
#[test]
fn test_sensor_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sensor_val", "sensor_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_sensor",
        "sensor_type == 1 || sensor_type == 2 || sensor_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensor type 1 (UV absorption) is valid 3-way disjunction",
    );
}

/// Test 5: Response time T90 (s) — bounded [1, 120], value 20.
#[test]
fn test_response_time_t90_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("t90_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume("t90_val", "t90_s == 20"));
    ctx.push_obligation(ProofObligation::assert("t90_min", "t90_s >= 1"));
    ctx.push_obligation(ProofObligation::assert("t90_max", "t90_s <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time T90 20 s in [1, 120]");
}

/// Test 6: Sample flow (mL/min) — bounded [100, 3000], value 1500.
#[test]
fn test_sample_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_ml_min", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_ml_min == 1500"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "flow_ml_min >= 100"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "flow_ml_min <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample flow 1500 mL/min in [100, 3000]");
}

/// Test 7: Output type — 4-way disjunction.
/// 1=4-20mA, 2=RS-485, 3=Ethernet, 4=Modbus. Value 1 (4-20mA).
#[test]
fn test_output_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("output_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("out_val", "output_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_output",
        "output_type == 1 || output_type == 2 || output_type == 3 || output_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output type 1 (4-20mA) is valid 4-way disjunction");
}

/// Test 8: Alarm levels — bounded [1, 5], value 3.
#[test]
fn test_alarm_levels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("alarm_levels", u32_ty());
    ctx.push_obligation(ProofObligation::assume("alarm_val", "alarm_levels == 3"));
    ctx.push_obligation(ProofObligation::assert("alarm_min", "alarm_levels >= 1"));
    ctx.push_obligation(ProofObligation::assert("alarm_max", "alarm_levels <= 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "alarm levels 3 in [1, 5]");
}

/// Test 9: Operating temperature offset +500 (deg C) — bounded [495, 545], value 520.
/// 495 represents -5°C, 520 represents 20°C, 545 represents 45°C.
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 495"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 545"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20 C (offset 520) in [495, 545]");
}

/// Test 10: Self-diagnostic — boolean flag using i32 with if/else pattern.
/// Flag 1 = self-diagnostic enabled, diagnostic_active = 1.
#[test]
fn test_self_diagnostic_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diag_flag", i32_ty());
    ctx.declare_var_typed("diagnostic_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "diag_flag == 0 || diag_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "diag_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "diag_def",
        "diagnostic_active == if diag_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diagnostic_enabled",
        "diagnostic_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "self-diagnostic flag enables diagnostic mode");
}
