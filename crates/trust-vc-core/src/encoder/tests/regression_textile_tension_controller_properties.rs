// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn tension_range_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tension_x100", u32_ty());
    // Tension in N scaled by 100: e.g., 5.50 N → 550, bounded [1, 100000]
    ctx.push_obligation(ProofObligation::assume(
        "tension_bounds",
        "tension_x100 >= 1 && tension_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tension_positive",
        "tension_x100 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tension_upper",
        "tension_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tension (x100 N) in [1, 100000] implies bounds hold",
    );
}

#[test]
fn line_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("line_speed", u32_ty());
    // Line speed in m/min, bounded [1, 2000]
    ctx.push_obligation(ProofObligation::assume(
        "speed_bounds",
        "line_speed >= 1 && line_speed <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert("speed_positive", "line_speed >= 1"));
    ctx.push_obligation(ProofObligation::assert("speed_upper", "line_speed <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "line speed in [1, 2000] m/min implies bounds hold");
}

#[test]
fn sensor_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sensor_type", u32_ty());
    // 1=load cell, 2=dancer arm, 3=ultrasonic
    ctx.push_obligation(ProofObligation::assume(
        "sensor_valid",
        "sensor_type == 1 || sensor_type == 2 || sensor_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sensor_in_range",
        "sensor_type >= 1 && sensor_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3-way sensor type disjunction implies [1,3] range");
}

#[test]
fn material_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material_type", u32_ty());
    // 1=yarn, 2=fabric, 3=wire, 4=film
    ctx.push_obligation(ProofObligation::assume(
        "material_valid",
        "material_type == 1 || material_type == 2 || material_type == 3 || material_type == 4",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_in_range",
        "material_type >= 1 && material_type <= 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "4-way material type disjunction implies [1,4] range",
    );
}

#[test]
fn control_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("control_mode", u32_ty());
    // 1=open loop, 2=closed loop, 3=cascade
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "control_mode == 1 || control_mode == 2 || control_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_in_range",
        "control_mode >= 1 && control_mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "3-way control mode disjunction implies [1,3] range",
    );
}

#[test]
fn roller_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("roller_count", u32_ty());
    // Roller count bounded [1, 20]
    ctx.push_obligation(ProofObligation::assume(
        "roller_bounds",
        "roller_count >= 1 && roller_count <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "roller_positive",
        "roller_count >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "roller_upper",
        "roller_count <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roller count in [1, 20] implies bounds hold");
}

#[test]
fn web_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("web_width_mm", u32_ty());
    // Web width in mm, bounded [10, 5000]
    ctx.push_obligation(ProofObligation::assume(
        "width_bounds",
        "web_width_mm >= 10 && web_width_mm <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert("width_lower", "web_width_mm >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "width_upper",
        "web_width_mm <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "web width in [10, 5000] mm implies bounds hold");
}

#[test]
fn accuracy_scaled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("accuracy_x10", u32_ty());
    // Accuracy in % scaled by 10: e.g., 0.5% → 5, bounded [1, 50]
    ctx.push_obligation(ProofObligation::assume(
        "accuracy_bounds",
        "accuracy_x10 >= 1 && accuracy_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_positive",
        "accuracy_x10 >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "accuracy_upper",
        "accuracy_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy (x10 %) in [1, 50] implies bounds hold");
}

#[test]
fn operating_temp_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    // Operating temperature in C with +500 offset: e.g., 25C → 525
    // Bounded [450, 600] meaning -50C to 100C
    ctx.push_obligation(ProofObligation::assume(
        "temp_bounds",
        "temp_offset >= 450 && temp_offset <= 600",
    ));
    // Verify offset encoding: 500 is 0C, 450 is -50C, 600 is 100C
    ctx.push_obligation(ProofObligation::assert("temp_lower", "temp_offset >= 450"));
    ctx.push_obligation(ProofObligation::assert("temp_upper", "temp_offset <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp offset [450, 600] implies bounds hold",
    );
}

#[test]
fn break_detection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("break_detected", i32_ty());
    ctx.declare_var_typed("emergency_stop", i32_ty());
    // Boolean flag: break_detected is 0 or 1
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "break_detected == 0 || break_detected == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_set", "break_detected == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "stop_def",
        "emergency_stop == if break_detected == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stop_active",
        "emergency_stop == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "break detected flag triggers emergency stop");
}
