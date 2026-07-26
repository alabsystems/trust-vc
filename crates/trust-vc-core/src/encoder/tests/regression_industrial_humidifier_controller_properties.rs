// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial humidifier controller property verification.
// Encodes key parameters of an industrial humidification system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Capacity (kg/h) — steam output bounded [1, 500], value 65.
#[test]
fn test_steam_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steam_kgh", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "steam_kgh == 65"));
    ctx.push_obligation(ProofObligation::assert("cap_min", "steam_kgh >= 1"));
    ctx.push_obligation(ProofObligation::assert("cap_max", "steam_kgh <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "steam capacity 65 kg/h in [1, 500]");
}

/// Test 2: Humidity setpoint (x10 %RH) — 50.0% = 500, bounded [100, 950].
#[test]
fn test_humidity_setpoint_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("setpoint_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sp_val", "setpoint_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("sp_min", "setpoint_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("sp_max", "setpoint_x10 <= 950"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "humidity setpoint 50.0% RH (500 x10) in [100, 950]",
    );
}

/// Test 3: Humidifier type — 4-way disjunction.
/// 1=electrode, 2=resistive, 3=ultrasonic, 4=evaporative. Value 3 (ultrasonic).
#[test]
fn test_humidifier_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("humidifier_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("type_val", "humidifier_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "humidifier_type == 1 || humidifier_type == 2 || humidifier_type == 3 || humidifier_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "humidifier type 3 (ultrasonic) is valid 4-way disjunction",
    );
}

/// Test 4: Water conductivity (uS/cm) — bounded [1, 2000], value 350.
#[test]
fn test_water_conductivity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conductivity", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cond_val", "conductivity == 350"));
    ctx.push_obligation(ProofObligation::assert("cond_min", "conductivity >= 1"));
    ctx.push_obligation(ProofObligation::assert("cond_max", "conductivity <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "water conductivity 350 uS/cm in [1, 2000]");
}

/// Test 5: Cylinder life (hours) — bounded [100, 10000], value 2500.
#[test]
fn test_cylinder_life_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cylinder_hrs", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cyl_val", "cylinder_hrs == 2500"));
    ctx.push_obligation(ProofObligation::assert("cyl_min", "cylinder_hrs >= 100"));
    ctx.push_obligation(ProofObligation::assert("cyl_max", "cylinder_hrs <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cylinder life 2500 hours in [100, 10000]");
}

/// Test 6: Control mode — 3-way disjunction.
/// 1=on-off, 2=proportional, 3=PID. Value 3 (PID).
#[test]
fn test_control_mode_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl_mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ctrl_val", "ctrl_mode == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_ctrl",
        "ctrl_mode == 1 || ctrl_mode == 2 || ctrl_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "control mode 3 (PID) is valid 3-way disjunction");
}

/// Test 7: Supply voltage (mV) — bounded [100000, 480000] (100V-480V), value 230000 (230V).
#[test]
fn test_supply_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage_mv", u32_ty());
    ctx.push_obligation(ProofObligation::assume("volt_val", "voltage_mv == 230000"));
    ctx.push_obligation(ProofObligation::assert("volt_min", "voltage_mv >= 100000"));
    ctx.push_obligation(ProofObligation::assert("volt_max", "voltage_mv <= 480000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "supply voltage 230V (230000 mV) in [100000, 480000]",
    );
}

/// Test 8: Drain interval (min) — bounded [1, 1440], value 120 (every 2 hours).
#[test]
fn test_drain_interval_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drain_min", u32_ty());
    ctx.push_obligation(ProofObligation::assume("drain_val", "drain_min == 120"));
    ctx.push_obligation(ProofObligation::assert("drain_lo", "drain_min >= 1"));
    ctx.push_obligation(ProofObligation::assert("drain_hi", "drain_min <= 1440"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drain interval 120 min in [1, 1440]");
}

/// Test 9: Operating temperature offset +500 (deg C) — bounded [450, 580].
/// 450 represents -50 C, 580 represents 80 C. Value 520 (20 C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 450"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 580"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20 C (offset 520) in [450, 580]");
}

/// Test 10: Low water alarm — boolean flag using i32 with if/else pattern.
/// Flag 1 = low water detected, which triggers alarm (alarm_active = 1).
#[test]
fn test_low_water_alarm_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("low_water_flag", i32_ty());
    ctx.declare_var_typed("alarm_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "low_water_flag == 0 || low_water_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "low_water_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_def",
        "alarm_active == if low_water_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "alarm_triggered",
        "alarm_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "low water flag triggers alarm");
}
