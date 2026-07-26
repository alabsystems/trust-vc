// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial fan (ventilation) controller property verification.
// Encodes key parameters of an industrial ventilation system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Air flow (m³/h) — volumetric flow rate bounded [100, 500000], value 10000.
#[test]
fn test_air_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_flow", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "air_flow == 10000"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "air_flow >= 100"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "air_flow <= 500000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow 10000 m3/h in [100, 500000]");
}

/// Test 2: Static pressure (Pa) — system pressure bounded [50, 10000], value 1500.
#[test]
fn test_static_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("static_pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_val",
        "static_pressure == 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_min",
        "static_pressure >= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_max",
        "static_pressure <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "static pressure 1500 Pa in [50, 10000]");
}

/// Test 3: Motor power (kW) — drive power bounded [1, 1000], value 55.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("motor_val", "motor_kw == 55"));
    ctx.push_obligation(ProofObligation::assert("motor_min", "motor_kw >= 1"));
    ctx.push_obligation(ProofObligation::assert("motor_max", "motor_kw <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 55 kW in [1, 1000]");
}

/// Test 4: Fan type — 4-way disjunction.
/// 1=centrifugal, 2=axial, 3=mixed-flow, 4=crossflow. Value 1 (centrifugal).
#[test]
fn test_fan_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fan_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fan_val", "fan_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_fan",
        "fan_type == 1 || fan_type == 2 || fan_type == 3 || fan_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fan type 1 (centrifugal) is valid 4-way disjunction",
    );
}

/// Test 5: Speed control — 3-way disjunction.
/// 1=direct-on-line, 2=VFD, 3=damper. Value 2 (VFD).
#[test]
fn test_speed_control_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_ctrl", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ctrl_val", "speed_ctrl == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_ctrl",
        "speed_ctrl == 1 || speed_ctrl == 2 || speed_ctrl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed control 2 (VFD) is valid 3-way disjunction");
}

/// Test 6: Blade count — impeller blade count bounded [3, 24], value 12.
#[test]
fn test_blade_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("blade_val", "blade_count == 12"));
    ctx.push_obligation(ProofObligation::assert("blade_min", "blade_count >= 3"));
    ctx.push_obligation(ProofObligation::assert("blade_max", "blade_count <= 24"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blade count 12 in [3, 24]");
}

/// Test 7: Efficiency (x10 percent) — fan efficiency bounded [500, 950], value 820 (82.0%).
#[test]
fn test_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("eff_val", "eff_x10 == 820"));
    ctx.push_obligation(ProofObligation::assert("eff_min", "eff_x10 >= 500"));
    ctx.push_obligation(ProofObligation::assert("eff_max", "eff_x10 <= 950"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fan efficiency 82.0% (820 x10) in [500, 950]");
}

/// Test 8: Noise level (dBA) — sound power level bounded [40, 120], value 85.
#[test]
fn test_noise_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("noise_dba", u32_ty());
    ctx.push_obligation(ProofObligation::assume("noise_val", "noise_dba == 85"));
    ctx.push_obligation(ProofObligation::assert("noise_min", "noise_dba >= 40"));
    ctx.push_obligation(ProofObligation::assert("noise_max", "noise_dba <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "noise level 85 dBA in [40, 120]");
}

/// Test 9: Operating temperature offset +500 (deg C) — bounded [460, 750], value 525.
/// 525 represents 25°C (525 - 500), 460 represents -40°C, 750 represents 250°C.
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 460"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 750"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 25 C (offset 525) in [460, 750]");
}

/// Test 10: Vibration monitor — boolean flag using i32 with if/else pattern.
/// Flag 1 = vibration monitoring enabled, which triggers alarm threshold at 10 mm/s.
#[test]
fn test_vibration_monitor_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vib_monitor", i32_ty());
    ctx.declare_var_typed("alarm_threshold", u32_ty());
    ctx.declare_var_typed("effective_threshold", u32_ty());
    ctx.declare_var_typed("no_limit", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "vib_monitor == 1"));
    ctx.push_obligation(ProofObligation::assume("no_limit_val", "no_limit == 9999"));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_val",
        "alarm_threshold == 10",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "threshold_def",
        "effective_threshold == if vib_monitor == 1 { alarm_threshold } else { no_limit }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "monitor_limits_vibration",
        "effective_threshold <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration monitor flag limits threshold to 10 mm/s",
    );
}
