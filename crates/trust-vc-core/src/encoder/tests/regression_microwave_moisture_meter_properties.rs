// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Microwave moisture meter property verification.
// Encodes key parameters of a microwave moisture meter and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Moisture range (x100 %) — 50.00% = 5000, bounded [100, 10000].
#[test]
fn test_moisture_range_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moisture_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mr_val", "moisture_x100 == 5000"));
    ctx.push_obligation(ProofObligation::assert("mr_min", "moisture_x100 >= 100"));
    ctx.push_obligation(ProofObligation::assert("mr_max", "moisture_x100 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "moisture 50.00% (5000 x100) in [100, 10000]");
}

/// Test 2: Accuracy (x100 %) — 0.20% = 20, bounded [1, 100].
#[test]
fn test_accuracy_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ac_val", "accuracy_x100 == 20"));
    ctx.push_obligation(ProofObligation::assert("ac_min", "accuracy_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("ac_max", "accuracy_x100 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 0.20% (20 x100) in [1, 100]");
}

/// Test 3: Frequency (GHz scaled x10) — 2.4 GHz = 24, bounded [10, 250].
#[test]
fn test_frequency_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fr_val", "freq_x10 == 24"));
    ctx.push_obligation(ProofObligation::assert("fr_min", "freq_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("fr_max", "freq_x10 <= 250"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "frequency 2.4 GHz (24 x10) in [10, 250]");
}

/// Test 4: Sensor type — 3-way disjunction.
/// 1=transmission, 2=reflection, 3=resonance. Value 1 (transmission).
#[test]
fn test_sensor_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("st_val", "sensor_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_sensor_type",
        "sensor_type == 1 || sensor_type == 2 || sensor_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensor type 1 (transmission) is valid 3-way disjunction",
    );
}

/// Test 5: Material type — 4-way disjunction.
/// 1=grain, 2=wood, 3=textile, 4=paper. Value 2 (wood).
#[test]
fn test_material_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mt_val", "material_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material_type",
        "material_type == 1 || material_type == 2 || material_type == 3 || material_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material type 2 (wood) is valid 4-way disjunction");
}

/// Test 6: Measurement speed (ms) — bounded [1, 1000], value 50.
#[test]
fn test_measurement_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_ms", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ms_val", "speed_ms == 50"));
    ctx.push_obligation(ProofObligation::assert("ms_min", "speed_ms >= 1"));
    ctx.push_obligation(ProofObligation::assert("ms_max", "speed_ms <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement speed 50 ms in [1, 1000]");
}

/// Test 7: Communication protocol — 3-way disjunction.
/// 1=4-20mA, 2=Modbus, 3=Profinet. Value 2 (Modbus).
#[test]
fn test_communication_protocol_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm_proto", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cp_val", "comm_proto == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm_proto",
        "comm_proto == 1 || comm_proto == 2 || comm_proto == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "communication protocol 2 (Modbus) is valid 3-way disjunction",
    );
}

/// Test 8: Penetration depth (mm) — bounded [10, 1000], value 300.
#[test]
fn test_penetration_depth_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("depth_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pd_val", "depth_mm == 300"));
    ctx.push_obligation(ProofObligation::assert("pd_min", "depth_mm >= 10"));
    ctx.push_obligation(ProofObligation::assert("pd_max", "depth_mm <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "penetration depth 300 mm in [10, 1000]");
}

/// Test 9: Operating temperature (deg C) — offset +500, bounded [460, 580].
/// Real range: -40 C to 80 C. Value 20 C → 520 with offset.
#[test]
fn test_operating_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("op_temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ot_val", "op_temp_off == 520"));
    ctx.push_obligation(ProofObligation::assert("ot_min", "op_temp_off >= 460"));
    ctx.push_obligation(ProofObligation::assert("ot_max", "op_temp_off <= 580"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp 20 C (offset +500: 520) in [460, 580]",
    );
}

/// Test 10: Temperature compensation — boolean flag using i32.
/// Flag 1 = compensation enabled. Assert derived value equals 1.
#[test]
fn test_temperature_compensation_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_comp_flag", i32_ty());
    ctx.declare_var_typed("comp_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_is_bool",
        "temp_comp_flag == 0 || temp_comp_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "temp_comp_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "comp_def",
        "comp_active == if temp_comp_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "comp_triggered",
        "comp_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature compensation flag activates compensation",
    );
}
