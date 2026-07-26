// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial tray dryer oven property verification.
// Encodes key parameters of a batch drying oven with removable trays used in
// pharmaceutical, food, and chemical drying applications, and verifies that
// they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Number of trays — bounded [4, 100].
#[test]
fn test_tray_dryer_oven_num_trays_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_trays", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trays_range",
        "num_trays >= 4 && num_trays <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trays_bounded",
        "num_trays >= 4 && num_trays <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of trays should be bounded to 4-100");
}

/// Test 2: Tray area x10 (m^2) — bounded [5, 500] representing 0.5-50.0 m^2.
#[test]
fn test_tray_dryer_oven_tray_area_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tray_area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "tray_area_x10 >= 5 && tray_area_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_bounded",
        "tray_area_x10 >= 5 && tray_area_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tray area x10 should be bounded to 5-500 (0.5-50.0 m2)",
    );
}

/// Test 3: Operating temperature offset+100 (deg C) — bounded [130, 500].
/// 130 represents 30 C, 500 represents 400 C.
#[test]
fn test_tray_dryer_oven_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_offset >= 130 && temp_offset <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_offset >= 130 && temp_offset <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp offset+100 should be bounded to 130-500 (30-400C)",
    );
}

/// Test 4: Air velocity x10 (m/s) — bounded [5, 100] representing 0.5-10.0 m/s.
#[test]
fn test_tray_dryer_oven_air_velocity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vel_range",
        "vel_x10 >= 5 && vel_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vel_bounded",
        "vel_x10 >= 5 && vel_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air velocity x10 should be bounded to 5-100 (0.5-10.0 m/s)",
    );
}

/// Test 5: Total capacity (kg) — bounded [10, 10000].
#[test]
fn test_tray_dryer_oven_total_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_kg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cap_range",
        "capacity_kg >= 10 && capacity_kg <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cap_bounded",
        "capacity_kg >= 10 && capacity_kg <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total capacity should be bounded to 10-10000 kg");
}

/// Test 6: Number of heating zones — bounded [1, 8].
#[test]
fn test_tray_dryer_oven_heating_zones_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zones", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "zones_range",
        "zones >= 1 && zones <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "zones_bounded",
        "zones >= 1 && zones <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of heating zones should be bounded to 1-8");
}

/// Test 7: Airflow pattern — 3-way disjunction.
/// 1=horizontal, 2=vertical, 3=combination.
#[test]
fn test_tray_dryer_oven_airflow_pattern_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("airflow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "airflow_valid",
        "airflow == 1 || airflow == 2 || airflow == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "airflow_bounded",
        "airflow == 1 || airflow == 2 || airflow == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "airflow pattern should be 1=horizontal, 2=vertical, or 3=combination",
    );
}

/// Test 8: Heating method — 3-way disjunction.
/// 1=electric, 2=steam, 3=gas.
#[test]
fn test_tray_dryer_oven_heating_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "heat_valid",
        "heat_method == 1 || heat_method == 2 || heat_method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "heat_bounded",
        "heat_method == 1 || heat_method == 2 || heat_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method should be 1=electric, 2=steam, or 3=gas",
    );
}

/// Test 9: Control mode — 3-way disjunction.
/// 1=temperature, 2=humidity, 3=combined.
#[test]
fn test_tray_dryer_oven_control_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_valid",
        "ctrl_mode == 1 || ctrl_mode == 2 || ctrl_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ctrl_bounded",
        "ctrl_mode == 1 || ctrl_mode == 2 || ctrl_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "control mode should be 1=temperature, 2=humidity, or 3=combined",
    );
}

/// Test 10: Automatic damper control — boolean flag (0 or 1).
#[test]
fn test_tray_dryer_oven_auto_damper_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_damper", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "damper_valid",
        "auto_damper == 0 || auto_damper == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "damper_bounded",
        "auto_damper == 0 || auto_damper == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "automatic damper control flag should be 0 or 1");
}
