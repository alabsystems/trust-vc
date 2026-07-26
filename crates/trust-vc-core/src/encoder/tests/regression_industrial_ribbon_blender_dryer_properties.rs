// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial ribbon blender dryer property verification.
// Encodes key parameters of an industrial ribbon blender dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Working volume (x10 L) — vessel working volume bounded [10, 500000].
/// 20000 represents 2000.0 L. Value 20000 (2000.0 L working volume).
#[test]
fn test_working_volume_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "volume_x10 == 20000"));
    ctx.push_obligation(ProofObligation::assert("vol_min", "volume_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("vol_max", "volume_x10 <= 500000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "working volume 2000.0 L (20000 x10) in [10, 500000]",
    );
}

/// Test 2: Ribbon speed (RPM) — agitator ribbon rotational speed bounded [1, 100], value 20.
#[test]
fn test_ribbon_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_rpm == 20"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_rpm >= 1"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_rpm <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ribbon speed 20 RPM in [1, 100]");
}

/// Test 3: Jacket temperature (offset +100 deg C) — bounded [100, 500].
/// 220 represents 120.0 deg C. Value 220 (120 deg C jacket temperature).
#[test]
fn test_jacket_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume("jt_val", "jacket_temp_off == 220"));
    ctx.push_obligation(ProofObligation::assert("jt_min", "jacket_temp_off >= 100"));
    ctx.push_obligation(ProofObligation::assert("jt_max", "jacket_temp_off <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature 120 C (220 offset+100) in [100, 500]",
    );
}

/// Test 4: Motor power (x10 kW) — drive motor rated power bounded [10, 5000].
/// 150 represents 15.0 kW. Value 150 (15.0 kW motor power).
#[test]
fn test_motor_power_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "motor_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert("pwr_min", "motor_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("pwr_max", "motor_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 15.0 kW (150 x10) in [10, 5000]");
}

/// Test 5: Vacuum level (x10 mbar) — process vacuum bounded [1, 10000].
/// 200 represents 20.0 mbar. Value 200 (20.0 mbar vacuum level).
#[test]
fn test_vacuum_level_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vacuum_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vacuum_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vacuum_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 20.0 mbar (200 x10) in [1, 10000]");
}

/// Test 6: Ribbon pitch (x10 mm) — helical ribbon pitch bounded [50, 5000].
/// 500 represents 50.0 mm. Value 500 (50.0 mm ribbon pitch).
#[test]
fn test_ribbon_pitch_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pitch_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pitch_val", "pitch_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("pitch_min", "pitch_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("pitch_max", "pitch_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ribbon pitch 50.0 mm (500 x10) in [50, 5000]");
}

/// Test 7: Ribbon type — 3-way disjunction.
/// 1=single-ribbon, 2=double-ribbon, 3=interrupted-ribbon. Value 2 (double-ribbon).
#[test]
fn test_ribbon_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ribbon_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rtype_val", "ribbon_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_ribbon",
        "ribbon_type == 1 || ribbon_type == 2 || ribbon_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ribbon type 2 (double-ribbon) is valid 3-way disjunction",
    );
}

/// Test 8: Discharge method — 3-way disjunction.
/// 1=center-bottom, 2=end-discharge, 3=full-length-bottom. Value 1 (center-bottom).
#[test]
fn test_discharge_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dm_val", "discharge_method == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_discharge",
        "discharge_method == 1 || discharge_method == 2 || discharge_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge method 1 (center-bottom) is valid 3-way disjunction",
    );
}

/// Test 9: Shaft seal — 3-way disjunction.
/// 1=packing-gland, 2=mechanical, 3=gas-purge. Value 2 (mechanical).
#[test]
fn test_shaft_seal_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shaft_seal", u32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "shaft_seal == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal",
        "shaft_seal == 1 || shaft_seal == 2 || shaft_seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shaft seal 2 (mechanical) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic fill-level control — boolean flag using i32 with if/else pattern.
/// Flag 1 = fill-level control enabled, which activates level monitoring (level_active = 1).
#[test]
fn test_automatic_fill_level_control_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fill_flag", i32_ty());
    ctx.declare_var_typed("level_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "fill_flag == 0 || fill_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "fill_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "level_def",
        "level_active == if fill_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("level_on", "level_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fill-level control flag activates level monitoring",
    );
}
