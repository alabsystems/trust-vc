// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Neutron moisture gauge property verification.
// Encodes key parameters of a neutron moisture gauge and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Moisture reading (x100 %) — 25.00% = 2500, bounded [0, 10000].
#[test]
fn test_moisture_reading_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moisture_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mr_val", "moisture_x100 == 2500"));
    ctx.push_obligation(ProofObligation::assert("mr_min", "moisture_x100 >= 0"));
    ctx.push_obligation(ProofObligation::assert("mr_max", "moisture_x100 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "moisture 25.00% (2500 x100) in [0, 10000]");
}

/// Test 2: Accuracy (x100 %) — 0.25% = 25, bounded [1, 500].
#[test]
fn test_accuracy_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ac_val", "accuracy_x100 == 25"));
    ctx.push_obligation(ProofObligation::assert("ac_min", "accuracy_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("ac_max", "accuracy_x100 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 0.25% (25 x100) in [1, 500]");
}

/// Test 3: Source type — 3-way disjunction.
/// 1=Cf-252, 2=Am-Be, 3=tube generator. Value 1 (Cf-252).
#[test]
fn test_source_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("st_val", "source_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_source_type",
        "source_type == 1 || source_type == 2 || source_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "source type 1 (Cf-252) is valid 3-way disjunction");
}

/// Test 4: Measurement depth (mm) — bounded [50, 2000], value 300.
#[test]
fn test_measurement_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("md_val", "depth_mm == 300"));
    ctx.push_obligation(ProofObligation::assert("md_min", "depth_mm >= 50"));
    ctx.push_obligation(ProofObligation::assert("md_max", "depth_mm <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement depth 300 mm in [50, 2000]");
}

/// Test 5: Response time (s) — bounded [1, 300], value 10.
#[test]
fn test_response_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("response_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rt_val", "response_s == 10"));
    ctx.push_obligation(ProofObligation::assert("rt_min", "response_s >= 1"));
    ctx.push_obligation(ProofObligation::assert("rt_max", "response_s <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "response time 10 s in [1, 300]");
}

/// Test 6: Detector type — 3-way disjunction.
/// 1=BF3, 2=He-3, 3=Li-6. Value 2 (He-3).
#[test]
fn test_detector_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dt_val", "detector_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_detector_type",
        "detector_type == 1 || detector_type == 2 || detector_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detector type 2 (He-3) is valid 3-way disjunction");
}

/// Test 7: Calibration points — bounded [2, 20], value 5.
#[test]
fn test_calibration_points_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal_points", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cp_val", "cal_points == 5"));
    ctx.push_obligation(ProofObligation::assert("cp_min", "cal_points >= 2"));
    ctx.push_obligation(ProofObligation::assert("cp_max", "cal_points <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "calibration points 5 in [2, 20]");
}

/// Test 8: Communication protocol — 3-way disjunction.
/// 1=4-20mA, 2=Modbus, 3=HART. Value 3 (HART).
#[test]
fn test_communication_protocol_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_proto", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cp_val", "comm_proto == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm_proto",
        "comm_proto == 1 || comm_proto == 2 || comm_proto == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "communication protocol 3 (HART) is valid 3-way disjunction",
    );
}

/// Test 9: Operating temperature (deg C) — offset +500, bounded [250, 800].
/// Real range: -250 C to 300 C. Value 25 C → 525 with offset.
#[test]
fn test_operating_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("op_temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ot_range",
        "op_temp_off >= 250 && op_temp_off <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert("ot_lower", "op_temp_off >= 250"));
    ctx.push_obligation(ProofObligation::assert("ot_upper", "op_temp_off <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp (offset +500) in [250, 800] implies bounds",
    );
}

/// Test 10: Radiation interlock — boolean flag using i32.
/// Flag 1 = interlock engaged, which activates safe mode (safe_mode = 1).
#[test]
fn test_radiation_interlock_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("interlock_flag", i32_ty());
    ctx.declare_var_typed("safe_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "interlock_flag == 0 || interlock_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "interlock_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "safe_mode_def",
        "safe_mode == if interlock_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "safe_mode_triggered",
        "safe_mode == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiation interlock flag activates safe mode");
}
