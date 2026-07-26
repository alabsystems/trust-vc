// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Digital torque wrench property verification.
// Encodes key parameters of a digital torque wrench and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Max torque (×10 Nm) — bounded [10, 20000].
/// 3400 represents 340.0 Nm. Value 3400 (typical mid-range wrench).
#[test]
fn test_max_torque_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("torque_val", "torque_x10 == 3400"));
    ctx.push_obligation(ProofObligation::assert("torque_min", "torque_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("torque_max", "torque_x10 <= 20000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max torque 340.0 Nm (3400 x10) in [10, 20000]");
}

/// Test 2: Accuracy (×10 % of reading) — bounded [5, 50].
/// 20 represents 2.0%. Value 20 (typical ±2% accuracy).
#[test]
fn test_accuracy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("acc_val", "accuracy_x10 == 20"));
    ctx.push_obligation(ProofObligation::assert("acc_min", "accuracy_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("acc_max", "accuracy_x10 <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy 2.0% (20 x10) in [5, 50]");
}

/// Test 3: Resolution (×100 Nm) — bounded [1, 100].
/// 10 represents 0.10 Nm. Value 10 (typical fine resolution).
#[test]
fn test_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "res_x100 == 10"));
    ctx.push_obligation(ProofObligation::assert("res_min", "res_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("res_max", "res_x100 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution 0.10 Nm (10 x100) in [1, 100]");
}

/// Test 4: Drive size — 4-way non-sequential disjunction.
/// 6=6mm, 10=10mm, 13=13mm, 19=19mm. Value 10 (10mm drive).
#[test]
fn test_drive_size_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", u32_ty());
    ctx.push_obligation(ProofObligation::assume("drive_val", "drive == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_drive",
        "drive == 6 || drive == 10 || drive == 13 || drive == 19",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive size 10 mm is valid 4-way disjunction");
}

/// Test 5: Mode — 3-way disjunction.
/// 1=peak, 2=track, 3=first-peak. Value 2 (track mode).
#[test]
fn test_mode_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "mode == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mode 2 (track) is valid 3-way disjunction");
}

/// Test 6: Communication — 3-way disjunction.
/// 1=USB, 2=Bluetooth, 3=WiFi. Value 3 (WiFi).
#[test]
fn test_communication_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("comm_val", "comm == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_comm",
        "comm == 1 || comm == 2 || comm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "communication 3 (WiFi) is valid 3-way disjunction");
}

/// Test 7: Memory capacity (readings) — bounded [100, 10000].
/// Value 2000 (typical storage for 2000 readings).
#[test]
fn test_memory_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("memory", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mem_val", "memory == 2000"));
    ctx.push_obligation(ProofObligation::assert("mem_min", "memory >= 100"));
    ctx.push_obligation(ProofObligation::assert("mem_max", "memory <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "memory capacity 2000 readings in [100, 10000]");
}

/// Test 8: Battery life (hours) — bounded [5, 100].
/// Value 20 (typical 20-hour battery life).
#[test]
fn test_battery_life_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("battery", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bat_val", "battery == 20"));
    ctx.push_obligation(ProofObligation::assert("bat_min", "battery >= 5"));
    ctx.push_obligation(ProofObligation::assert("bat_max", "battery <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "battery life 20 hours in [5, 100]");
}

/// Test 9: Operating temperature offset +500 (deg C) — bounded [490, 550].
/// 490 represents -10 C, 550 represents 50 C. Value 520 (20 C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp == 520"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp >= 490"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp <= 550"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20 C (offset 520) in [490, 550]");
}

/// Test 10: Angle measurement — boolean flag using i32 with if/else pattern.
/// Flag 1 = angle measurement supported, active_reading = 1.
#[test]
fn test_angle_measurement_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_flag", i32_ty());
    ctx.declare_var_typed("active_reading", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "angle_flag == 0 || angle_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "angle_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "active_reading == if angle_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "angle_active",
        "active_reading == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "angle measurement flag enables active reading");
}
