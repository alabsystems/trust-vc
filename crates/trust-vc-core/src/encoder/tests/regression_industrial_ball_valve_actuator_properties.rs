// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial ball valve actuator property verification.
// Encodes key parameters of an industrial ball valve with actuator and verifies
// that they satisfy bounded, disjunctive, scaled, offset, and boolean-flag constraints.

/// Test 1: Valve size (mm) — nominal diameter bounded [15, 600], value 150.
#[test]
fn test_valve_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_size_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("size_val", "valve_size_mm == 150"));
    ctx.push_obligation(ProofObligation::assert("size_min", "valve_size_mm >= 15"));
    ctx.push_obligation(ProofObligation::assert("size_max", "valve_size_mm <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "valve size 150 mm in [15, 600]");
}

/// Test 2: Pressure rating (bar) — max allowable pressure bounded [10, 420], value 64.
#[test]
fn test_pressure_rating_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.push_obligation(ProofObligation::assume("press_val", "pressure_bar == 64"));
    ctx.push_obligation(ProofObligation::assert("press_min", "pressure_bar >= 10"));
    ctx.push_obligation(ProofObligation::assert("press_max", "pressure_bar <= 420"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure rating 64 bar in [10, 420]");
}

/// Test 3: Torque output (x10 Nm) — actuator torque scaled at 0.1 Nm.
/// Value 4500 represents 450.0 Nm, bounded [100, 50000] (10.0 to 5000.0 Nm).
#[test]
fn test_torque_output_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("torque_val", "torque_x10 == 4500"));
    ctx.push_obligation(ProofObligation::assert("torque_min", "torque_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("torque_max", "torque_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "torque output 450.0 Nm (4500 x10) in [100, 50000]");
}

/// Test 4: Operating temperature offset +500 (deg C) — bounded [460, 800].
/// 460 represents -40 C, 800 represents 300 C. Value 520 (20 C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 460"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20 C (offset 520) in [460, 800]");
}

/// Test 5: Cycle time (x10 s) — quarter-turn travel time scaled at 0.1 s.
/// Value 25 represents 2.5 s, bounded [5, 600] (0.5 to 60.0 s).
#[test]
fn test_cycle_time_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cycle_val", "cycle_x10 == 25"));
    ctx.push_obligation(ProofObligation::assert("cycle_min", "cycle_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("cycle_max", "cycle_x10 <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle time 2.5 s (25 x10) in [5, 600]");
}

/// Test 6: Actuator type — 3-way disjunction.
/// 1=pneumatic, 2=electric, 3=hydraulic. Value 2 (electric).
#[test]
fn test_actuator_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("actuator_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("act_val", "actuator_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_actuator",
        "actuator_type == 1 || actuator_type == 2 || actuator_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "actuator type 2 (electric) is valid 3-way disjunction",
    );
}

/// Test 7: Ball type — 3-way disjunction.
/// 1=full bore, 2=reduced bore, 3=V-port. Value 1 (full bore).
#[test]
fn test_ball_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ball_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ball_val", "ball_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_ball",
        "ball_type == 1 || ball_type == 2 || ball_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ball type 1 (full bore) is valid 3-way disjunction",
    );
}

/// Test 8: Seat material — 3-way disjunction.
/// 1=PTFE, 2=metal, 3=PEEK. Value 3 (PEEK).
#[test]
fn test_seat_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seat_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("seat_val", "seat_material == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seat",
        "seat_material == 1 || seat_material == 2 || seat_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seat material 3 (PEEK) is valid 3-way disjunction");
}

/// Test 9: Fail position — 3-way disjunction.
/// 1=fail-open, 2=fail-closed, 3=stay-put. Value 2 (fail-closed).
#[test]
fn test_fail_position_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fail_pos", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fail_val", "fail_pos == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_fail",
        "fail_pos == 1 || fail_pos == 2 || fail_pos == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fail position 2 (fail-closed) is valid 3-way disjunction",
    );
}

/// Test 10: Position feedback — boolean flag using i32 with if/else pattern.
/// Flag 1 = position feedback enabled, which activates position reporting.
#[test]
fn test_position_feedback_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feedback_flag", i32_ty());
    ctx.declare_var_typed("report_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "feedback_flag == 0 || feedback_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "feedback_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "report_def",
        "report_active == if feedback_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feedback_enables_report",
        "report_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "position feedback flag enables position reporting");
}
