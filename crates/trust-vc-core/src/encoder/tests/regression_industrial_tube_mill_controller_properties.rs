// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial tube mill controller property verification.
// Encodes key parameters of an industrial tube mill grinding system and verifies
// that they satisfy bounded, disjunctive, scaled, and boolean-flag constraints.

/// Test 1: Tube diameter (mm) — bounded [1000, 5000], value 3200.
#[test]
fn test_tube_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_dia_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "tube_dia_mm == 3200"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "tube_dia_mm >= 1000"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "tube_dia_mm <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube diameter 3200 mm in [1000, 5000]");
}

/// Test 2: Tube length (mm) — bounded [3000, 15000], value 9000.
#[test]
fn test_tube_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tube_len_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "tube_len_mm == 9000"));
    ctx.push_obligation(ProofObligation::assert("len_min", "tube_len_mm >= 3000"));
    ctx.push_obligation(ProofObligation::assert("len_max", "tube_len_mm <= 15000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube length 9000 mm in [3000, 15000]");
}

/// Test 3: Rotation speed (x10 RPM) — 150 represents 15.0 RPM, bounded [50, 300].
#[test]
fn test_rotation_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "speed_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "speed_x10 <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 15.0 RPM (150 x10) in [50, 300]");
}

/// Test 4: Motor power (kW) — bounded [100, 5000], value 2200.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("power_val", "motor_kw == 2200"));
    ctx.push_obligation(ProofObligation::assert("power_min", "motor_kw >= 100"));
    ctx.push_obligation(ProofObligation::assert("power_max", "motor_kw <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 2200 kW in [100, 5000]");
}

/// Test 5: Ball charge level (x10 %) — 350 represents 35.0%, bounded [200, 450].
#[test]
fn test_ball_charge_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("charge_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("charge_val", "charge_x10 == 350"));
    ctx.push_obligation(ProofObligation::assert("charge_min", "charge_x10 >= 200"));
    ctx.push_obligation(ProofObligation::assert("charge_max", "charge_x10 <= 450"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ball charge 35.0% (350 x10) in [200, 450]");
}

/// Test 6: Mill type — 3-way disjunction.
/// 1=overflow, 2=grate discharge, 3=air-swept. Value 2 (grate discharge).
#[test]
fn test_mill_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mill_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mtype_val", "mill_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mill_type",
        "mill_type == 1 || mill_type == 2 || mill_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mill type 2 (grate discharge) is valid 3-way disjunction",
    );
}

/// Test 7: Lining material — 3-way disjunction.
/// 1=rubber, 2=steel, 3=ceramic. Value 3 (ceramic).
#[test]
fn test_lining_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lining_mat", u32_ty());
    ctx.push_obligation(ProofObligation::assume("lining_val", "lining_mat == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_lining_mat",
        "lining_mat == 1 || lining_mat == 2 || lining_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "lining material 3 (ceramic) is valid 3-way disjunction",
    );
}

/// Test 8: Feed size (um) — bounded [1000, 50000], value 25000.
#[test]
fn test_feed_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_size_um", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_size_um == 25000"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_size_um >= 1000"));
    ctx.push_obligation(ProofObligation::assert("feed_max", "feed_size_um <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed size 25000 um in [1000, 50000]");
}

/// Test 9: Product fineness (x10 um) — 450 represents 45.0 um, bounded [100, 5000].
#[test]
fn test_product_fineness_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fineness_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fine_val", "fineness_x10 == 450"));
    ctx.push_obligation(ProofObligation::assert("fine_min", "fineness_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("fine_max", "fineness_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "product fineness 45.0 um (450 x10) in [100, 5000]");
}

/// Test 10: Automatic charge level — boolean flag using i32 with if/else pattern.
/// Flag 1 = auto charge enabled, which activates the charge controller (controller_active = 1).
#[test]
fn test_auto_charge_level_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_charge_flag", i32_ty());
    ctx.declare_var_typed("controller_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "auto_charge_flag == 0 || auto_charge_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_charge_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "controller_def",
        "controller_active == if auto_charge_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "controller_triggered",
        "controller_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto charge flag activates charge controller");
}
