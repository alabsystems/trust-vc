// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial paddle mixer dryer property verification.
// Encodes key parameters of an industrial paddle mixer dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Working volume (x10 L) — vessel working volume bounded [10, 100000].
/// 8000 represents 800.0 L. Value 8000 (800.0 L working volume).
#[test]
fn test_working_volume_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "volume_x10 == 8000"));
    ctx.push_obligation(ProofObligation::assert("vol_min", "volume_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("vol_max", "volume_x10 <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "working volume 800.0 L (8000 x10) in [10, 100000]");
}

/// Test 2: Paddle speed (RPM) — agitator rotational speed bounded [1, 200], value 30.
#[test]
fn test_paddle_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_rpm == 30"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_rpm >= 1"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_rpm <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paddle speed 30 RPM in [1, 200]");
}

/// Test 3: Jacket temperature (offset +100 deg C) — bounded [100, 500].
/// 250 represents 150.0 deg C. Value 250 (150 deg C jacket temperature).
#[test]
fn test_jacket_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume("jt_val", "jacket_temp_off == 250"));
    ctx.push_obligation(ProofObligation::assert("jt_min", "jacket_temp_off >= 100"));
    ctx.push_obligation(ProofObligation::assert("jt_max", "jacket_temp_off <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature 150 C (250 offset+100) in [100, 500]",
    );
}

/// Test 4: Torque (x10 Nm) — paddle shaft torque bounded [10, 100000].
/// 5000 represents 500.0 Nm. Value 5000 (500.0 Nm torque).
#[test]
fn test_torque_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("trq_val", "torque_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert("trq_min", "torque_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("trq_max", "torque_x10 <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "torque 500.0 Nm (5000 x10) in [10, 100000]");
}

/// Test 5: Vacuum level (x10 mbar) — process vacuum bounded [1, 10000].
/// 100 represents 10.0 mbar. Value 100 (10.0 mbar vacuum level).
#[test]
fn test_vacuum_level_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vacuum_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vacuum_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vacuum_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 10.0 mbar (100 x10) in [1, 10000]");
}

/// Test 6: Number of paddle arms — count bounded [2, 20], value 8.
#[test]
fn test_paddle_arm_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("paddle_arms", u32_ty());
    ctx.push_obligation(ProofObligation::assume("arms_val", "paddle_arms == 8"));
    ctx.push_obligation(ProofObligation::assert("arms_min", "paddle_arms >= 2"));
    ctx.push_obligation(ProofObligation::assert("arms_max", "paddle_arms <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paddle arm count 8 in [2, 20]");
}

/// Test 7: Paddle configuration — 3-way disjunction.
/// 1=single-shaft, 2=double-shaft, 3=counter-rotating. Value 2 (double-shaft).
#[test]
fn test_paddle_configuration_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("paddle_config", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pcfg_val", "paddle_config == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_config",
        "paddle_config == 1 || paddle_config == 2 || paddle_config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "paddle config 2 (double-shaft) is valid 3-way disjunction",
    );
}

/// Test 8: Heating method — 3-way disjunction.
/// 1=jacket-only, 2=jacket-plus-shaft, 3=jacket-plus-paddles. Value 3 (jacket-plus-paddles).
#[test]
fn test_heating_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hm_val", "heat_method == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heat",
        "heat_method == 1 || heat_method == 2 || heat_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method 3 (jacket-plus-paddles) is valid 3-way disjunction",
    );
}

/// Test 9: Seal type — 3-way disjunction.
/// 1=mechanical, 2=lip, 3=gas-purge. Value 1 (mechanical).
#[test]
fn test_seal_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type 1 (mechanical) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic endpoint detection — boolean flag using i32 with if/else pattern.
/// Flag 1 = endpoint detection enabled, which activates auto-stop (auto_stop = 1).
#[test]
fn test_automatic_endpoint_detection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("endpoint_flag", i32_ty());
    ctx.declare_var_typed("auto_stop", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "endpoint_flag == 0 || endpoint_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "endpoint_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "stop_def",
        "auto_stop == if endpoint_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("stop_active", "auto_stop == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "endpoint detection flag activates auto-stop");
}
