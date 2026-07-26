// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial conical screw dryer property verification.
// Encodes key parameters of an industrial conical screw dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Vessel volume (x10 L) — bounded [10, 100000], value 5000 (500.0 L).
#[test]
fn test_conical_screw_dryer_vessel_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_vol_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "vessel_vol_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert("vol_min", "vessel_vol_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "vol_max",
        "vessel_vol_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume 500.0 L (5000 x10) in [10, 100000]");
}

/// Test 2: Screw speed (RPM) — bounded [1, 200], value 20.
#[test]
fn test_conical_screw_dryer_screw_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("screw_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "screw_rpm == 20"));
    ctx.push_obligation(ProofObligation::assert("rpm_min", "screw_rpm >= 1"));
    ctx.push_obligation(ProofObligation::assert("rpm_max", "screw_rpm <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "screw speed 20 RPM in [1, 200]");
}

/// Test 3: Jacket temperature offset +100 (deg C) — bounded [100, 500], value 220.
/// 100 represents 0 C, 220 represents 120 C, 500 represents 400 C.
#[test]
fn test_conical_screw_dryer_jacket_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "jacket_temp_offset == 220",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "jacket_temp_offset >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "jacket_temp_offset <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jacket temp 120 C (offset 220) in [100, 500]");
}

/// Test 4: Vacuum level (x10 mbar) — bounded [1, 10000], value 100 (10.0 mbar).
#[test]
fn test_conical_screw_dryer_vacuum_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vacuum_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vacuum_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vacuum_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 10.0 mbar (100 x10) in [1, 10000]");
}

/// Test 5: Batch size (x10 kg) — bounded [1, 100000], value 500 (50.0 kg).
#[test]
fn test_conical_screw_dryer_batch_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("batch_val", "batch_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("batch_min", "batch_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("batch_max", "batch_x10 <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch size 50.0 kg (500 x10) in [1, 100000]");
}

/// Test 6: Cone angle (x10 degrees) — bounded [100, 600], value 300 (30.0 deg).
#[test]
fn test_conical_screw_dryer_cone_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cone_angle_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_val",
        "cone_angle_x10 == 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_min",
        "cone_angle_x10 >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_max",
        "cone_angle_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cone angle 30.0 deg (300 x10) in [100, 600]");
}

/// Test 7: Heating method — 3-way disjunction.
/// 1=steam, 2=hot-water, 3=thermal-oil. Value 1 (steam).
#[test]
fn test_conical_screw_dryer_heating_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume("heat_val", "heat_method == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heat_method",
        "heat_method == 1 || heat_method == 2 || heat_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method 1 (steam) is valid 3-way disjunction",
    );
}

/// Test 8: Screw type — 3-way disjunction.
/// 1=single-arm, 2=double-arm, 3=helical-ribbon. Value 1 (single-arm).
#[test]
fn test_conical_screw_dryer_screw_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("screw_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("screw_val", "screw_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_screw_type",
        "screw_type == 1 || screw_type == 2 || screw_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "screw type 1 (single-arm) is valid 3-way disjunction",
    );
}

/// Test 9: Discharge method — 3-way disjunction.
/// 1=bottom-valve, 2=side-port, 3=vacuum-discharge. Value 1 (bottom-valve).
#[test]
fn test_conical_screw_dryer_discharge_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dis_val", "discharge_method == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_discharge",
        "discharge_method == 1 || discharge_method == 2 || discharge_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge method 1 (bottom-valve) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic endpoint detection — boolean flag using i32 with if/else pattern.
/// Flag 1 = endpoint detection enabled, detection_active should be 1.
#[test]
fn test_conical_screw_dryer_auto_endpoint_detection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("endpoint_flag", i32_ty());
    ctx.declare_var_typed("detection_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "endpoint_flag == 0 || endpoint_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "endpoint_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "detection_def",
        "detection_active == if endpoint_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detection_enabled",
        "detection_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "endpoint flag triggers detection active");
}
