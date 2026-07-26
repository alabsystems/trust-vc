// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_flow_rate_scaled() {
    // Flow rate in ×10 L/min (0.1 L/min resolution)
    // 125 represents 12.5 L/min, must be in range [1, 5000] (0.1–500.0 L/min)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("fr", "flow_rate_x10 == 125"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if flow_rate_x10 >= 1 && flow_rate_x10 <= 5000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: flow 12.5 L/min in [0.1, 500.0]");
}

#[test]
fn test_max_pressure_bounded() {
    // Operating pressure in bar, bounded [50, 700]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("p", "pressure_bar == 350"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if pressure_bar >= 50 && pressure_bar <= 700 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: 350 bar in [50, 700]");
}

#[test]
fn test_piston_count_bounded() {
    // Number of pistons, bounded [1, 9]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("piston_count", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pc", "piston_count == 7"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if piston_count >= 1 && piston_count <= 9 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: 7 pistons in [1, 9]");
}

#[test]
fn test_stroke_length_scaled() {
    // Stroke length in ×10 mm (0.1 mm resolution)
    // 285 represents 28.5 mm, must be in range [10, 1000] (1.0–100.0 mm)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sl", "stroke_x10 == 285"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if stroke_x10 >= 10 && stroke_x10 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: stroke 28.5 mm in [1.0, 100.0]");
}

#[test]
fn test_motor_power_bounded() {
    // Motor power in kW, bounded [1, 500]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mk", "motor_kw == 75"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if motor_kw >= 1 && motor_kw <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: 75 kW motor in [1, 500]");
}

#[test]
fn test_pump_type_disjunction() {
    // Pump type: 1=axial, 2=radial, 3=inline
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pt", "pump_type == 2"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if pump_type == 1 || pump_type == 2 || pump_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: type radial (2) is valid");
}

#[test]
fn test_valve_type_disjunction() {
    // Valve type: 1=spring, 2=plate, 3=poppet
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_type", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vt", "valve_type == 3"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if valve_type == 1 || valve_type == 2 || valve_type == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: valve poppet (3) is valid");
}

#[test]
fn test_efficiency_scaled() {
    // Efficiency in ×10 % (0.1% resolution)
    // 925 represents 92.5%, must be in range [1, 1000] (0.1%–100.0%)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("eff", "efficiency_x10 == 925"));
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if efficiency_x10 >= 1 && efficiency_x10 <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: efficiency 92.5% in [0.1, 100.0]");
}

#[test]
fn test_speed_rpm_bounded() {
    // Rotational speed in RPM, bounded [500, 3000]
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sr", "speed_rpm == 1800"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if speed_rpm >= 500 && speed_rpm <= 3000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston pump: 1800 RPM in [500, 3000]");
}

#[test]
fn test_variable_displacement_flag() {
    // Variable displacement: i32 boolean flag (1=variable, 0=fixed)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("swashplate_angle", u32_ty());
    ctx.declare_var_typed("variable_displacement", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sa", "swashplate_angle == 15"));
    ctx.push_obligation(ProofObligation::assume(
        "vd_def",
        "variable_displacement == if swashplate_angle > 0 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_variable",
        "variable_displacement == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piston pump: swashplate 15 deg \u{2192} variable displacement",
    );
}
