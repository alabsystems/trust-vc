// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial twin screw extruder property verification.
// Encodes key parameters of an industrial twin screw extruder system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Screw diameter (mm) — bounded [20, 200], value 92.
#[test]
fn test_twin_screw_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "diameter == 92"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "diameter >= 20"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "diameter <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw diameter 92 mm in [20, 200]");
}

/// Test 2: L/D ratio — length-to-diameter ratio bounded [20, 60], value 40.
#[test]
fn test_twin_screw_ld_ratio_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ld_ratio", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ld_val", "ld_ratio == 40"));
    ctx.push_obligation(ProofObligation::assert("ld_min", "ld_ratio >= 20"));
    ctx.push_obligation(ProofObligation::assert("ld_max", "ld_ratio <= 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "L/D ratio 40 in [20, 60]");
}

/// Test 3: Screw speed (RPM) — bounded [50, 1200], value 600.
#[test]
fn test_twin_screw_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("screw_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "screw_rpm == 600"));
    ctx.push_obligation(ProofObligation::assert("rpm_min", "screw_rpm >= 50"));
    ctx.push_obligation(ProofObligation::assert("rpm_max", "screw_rpm <= 1200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw speed 600 RPM in [50, 1200]");
}

/// Test 4: Barrel temperature offset +500 (deg C) — bounded [650, 850].
/// 650 represents 150 C, 850 represents 350 C. Value 780 (280 C).
#[test]
fn test_twin_screw_barrel_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("barrel_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "barrel_temp_offset == 780",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "barrel_temp_offset >= 650",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "barrel_temp_offset <= 850",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "barrel temp 280 C (offset 780) in [650, 850]");
}

/// Test 5: Throughput (kg/h) — bounded [5, 5000], value 850.
#[test]
fn test_twin_screw_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_kgh", u32_ty());
    ctx.push_obligation(ProofObligation::assume("thr_val", "throughput_kgh == 850"));
    ctx.push_obligation(ProofObligation::assert("thr_min", "throughput_kgh >= 5"));
    ctx.push_obligation(ProofObligation::assert("thr_max", "throughput_kgh <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 850 kg/h in [5, 5000]");
}

/// Test 6: Rotation type — 3-way disjunction.
/// 1=co-rotating, 2=counter-rotating, 3=intermeshing. Value 1 (co-rotating).
#[test]
fn test_twin_screw_rotation_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotation_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rot_val", "rotation_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_rotation",
        "rotation_type == 1 || rotation_type == 2 || rotation_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "rotation type 1 (co-rotating) is valid 3-way disjunction",
    );
}

/// Test 7: Screw element — 3-way disjunction.
/// 1=conveying, 2=kneading, 3=mixing. Value 2 (kneading).
#[test]
fn test_twin_screw_element_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("screw_element", u32_ty());
    ctx.push_obligation(ProofObligation::assume("elem_val", "screw_element == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_element",
        "screw_element == 1 || screw_element == 2 || screw_element == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "screw element 2 (kneading) is valid 3-way disjunction",
    );
}

/// Test 8: Motor power (kW) — bounded [10, 1000], value 250.
#[test]
fn test_twin_screw_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "motor_kw == 250"));
    ctx.push_obligation(ProofObligation::assert("pwr_min", "motor_kw >= 10"));
    ctx.push_obligation(ProofObligation::assert("pwr_max", "motor_kw <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 250 kW in [10, 1000]");
}

/// Test 9: Torque (x10 Nm) — scaled at 0.1 Nm, bounded [100, 50000].
/// 100 represents 10.0 Nm, 50000 represents 5000.0 Nm. Value 12500 (1250.0 Nm).
#[test]
fn test_twin_screw_torque_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("torq_val", "torque_x10 == 12500"));
    ctx.push_obligation(ProofObligation::assert("torq_min", "torque_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("torq_max", "torque_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "torque 1250.0 Nm (12500 x10) in [100, 50000]");
}

/// Test 10: Degassing — boolean flag using i32 with if/else pattern.
/// Flag 1 = vacuum degassing port active, degassing_active = 1.
#[test]
fn test_twin_screw_degassing_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("degas_flag", i32_ty());
    ctx.declare_var_typed("degassing_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "degas_flag == 0 || degas_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "degas_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "degas_def",
        "degassing_active == if degas_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "degas_enabled",
        "degassing_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "degassing flag activates vacuum degassing port");
}
