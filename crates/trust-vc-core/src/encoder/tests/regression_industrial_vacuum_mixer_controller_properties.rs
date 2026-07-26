// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial vacuum mixer controller property verification.
// Encodes key parameters of an industrial vacuum mixer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Vessel volume (L) — bounded [50, 5000], value 1500.
#[test]
fn test_vessel_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_volume_l", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_val",
        "vessel_volume_l == 1500",
    ));
    ctx.push_obligation(ProofObligation::assert("vol_min", "vessel_volume_l >= 50"));
    ctx.push_obligation(ProofObligation::assert(
        "vol_max",
        "vessel_volume_l <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume 1500 L in [50, 5000]");
}

/// Test 2: Mixer speed (RPM) — bounded [10, 500], value 120.
#[test]
fn test_mixer_speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mixer_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "mixer_rpm == 120"));
    ctx.push_obligation(ProofObligation::assert("rpm_min", "mixer_rpm >= 10"));
    ctx.push_obligation(ProofObligation::assert("rpm_max", "mixer_rpm <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mixer speed 120 RPM in [10, 500]");
}

/// Test 3: Vacuum level (x10 mbar) — bounded [1, 10130].
/// 50 represents 5.0 mbar. Value 50.
#[test]
fn test_vacuum_level_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vacuum_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vacuum_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vacuum_x10 <= 10130"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 5.0 mbar (50 x10) in [1, 10130]");
}

/// Test 4: Motor power (kW) — bounded [1, 200], value 55.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "motor_kw == 55"));
    ctx.push_obligation(ProofObligation::assert("pwr_min", "motor_kw >= 1"));
    ctx.push_obligation(ProofObligation::assert("pwr_max", "motor_kw <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 55 kW in [1, 200]");
}

/// Test 5: Operating temperature offset +500 (deg C) — bounded [450, 700].
/// 450 represents -50 C, 700 represents 200 C. Value 580 (80 C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 580"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 450"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 700"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 80 C (offset 580) in [450, 700]");
}

/// Test 6: Blade type — 3-way disjunction.
/// 1=anchor, 2=helical, 3=butterfly. Value 2 (helical).
#[test]
fn test_blade_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("blade_val", "blade_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_blade",
        "blade_type == 1 || blade_type == 2 || blade_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blade type 2 (helical) is valid 3-way disjunction");
}

/// Test 7: Seal type — 3-way disjunction.
/// 1=mechanical, 2=lip seal, 3=magnetic coupling. Value 3 (magnetic coupling).
#[test]
fn test_seal_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type 3 (magnetic coupling) is valid 3-way disjunction",
    );
}

/// Test 8: Batch weight (kg) — bounded [10, 3000], value 750.
#[test]
fn test_batch_weight_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_kg", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wt_val", "batch_kg == 750"));
    ctx.push_obligation(ProofObligation::assert("wt_min", "batch_kg >= 10"));
    ctx.push_obligation(ProofObligation::assert("wt_max", "batch_kg <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch weight 750 kg in [10, 3000]");
}

/// Test 9: Torque limit (x10 Nm) — bounded [10, 50000].
/// 3500 represents 350.0 Nm. Value 3500.
#[test]
fn test_torque_limit_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("trq_val", "torque_x10 == 3500"));
    ctx.push_obligation(ProofObligation::assert("trq_min", "torque_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("trq_max", "torque_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "torque limit 350.0 Nm (3500 x10) in [10, 50000]");
}

/// Test 10: Auto-deaeration — boolean flag using i32 with if/else pattern.
/// Flag 1 = auto-deaeration enabled, vacuum_pump_active = 1.
#[test]
fn test_auto_deaeration_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("deaeration_flag", i32_ty());
    ctx.declare_var_typed("vacuum_pump_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "deaeration_flag == 0 || deaeration_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "deaeration_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "pump_def",
        "vacuum_pump_active == if deaeration_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pump_enabled",
        "vacuum_pump_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-deaeration flag activates vacuum pump");
}
