// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_linear_motor_compressor_piston_stroke_range() {
    // Piston stroke at x10 mm: physical range 5.0–50.0 mm -> 50–500 scaled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stroke_bounds_a",
        "stroke_x10 >= 50 && stroke_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_positive_c",
        "stroke_x10 > 0",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston stroke in [50,500] is strictly positive");
}

#[test]
fn test_linear_motor_compressor_operating_frequency_range() {
    // Operating frequency at x10 Hz: physical range 30.0–120.0 Hz -> 300–1200 scaled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_bounds_a",
        "freq_x10 >= 300 && freq_x10 <= 1200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_above_mains_c",
        "freq_x10 >= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating frequency in [300,1200] is at least mains frequency",
    );
}

#[test]
fn test_linear_motor_compressor_discharge_pressure_range() {
    // Discharge pressure at x10 bar: physical range 1.0–40.0 bar -> 10–400 scaled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_bounds_a",
        "press_x10 >= 10 && press_x10 <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded_c",
        "press_x10 >= 10 && press_x10 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure stays within safe operating envelope",
    );
}

#[test]
fn test_linear_motor_compressor_discharge_temperature_offset() {
    // Discharge temperature offset +100 degC: physical range 20–250 degC -> 120–350 offset
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_bounds_a",
        "temp_off >= 120 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_above_freezing_c",
        "temp_off > 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge temp offset [120,350] is always above 0 degC (offset 100)",
    );
}

#[test]
fn test_linear_motor_compressor_motor_current_range() {
    // Motor current at x100 A: physical range 0.1–200.0 A -> 10–20000 scaled
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_bounds_a",
        "curr_x100 >= 10 && curr_x100 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert("curr_nonzero_c", "curr_x100 >= 10"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor current in [10,20000] guarantees minimum draw",
    );
}

#[test]
fn test_linear_motor_compressor_cooling_capacity_watts() {
    // Cooling capacity in watts: 50–5000 W
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "capacity_bounds_a",
        "capacity >= 50 && capacity <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_positive_c",
        "capacity >= 50 && capacity <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling capacity in [50,5000] W stays within rated range",
    );
}

#[test]
fn test_linear_motor_compressor_refrigerant_type() {
    // Refrigerant type: 3-way enum (1=R600a, 2=R134a, 3=R290)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrigerant", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "refrigerant_valid_a",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "refrigerant_in_range_c",
        "refrigerant >= 1 && refrigerant <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3-way refrigerant type is always in [1,3]");
}

#[test]
fn test_linear_motor_compressor_spring_type() {
    // Spring type: 3-way enum (1=mechanical, 2=gas, 3=planar)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spring", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spring_valid_a",
        "spring == 1 || spring == 2 || spring == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spring_in_range_c",
        "spring >= 1 && spring <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3-way spring type is always in [1,3]");
}

#[test]
fn test_linear_motor_compressor_control_mode() {
    // Control mode: 3-way enum (1=resonance, 2=stroke-control, 3=capacity-modulation)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid_a",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_in_range_c",
        "mode >= 1 && mode <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "3-way control mode is always in [1,3]");
}

#[test]
fn test_linear_motor_compressor_auto_stroke_optimization_flag() {
    // Auto stroke optimization: boolean flag (0=disabled, 1=enabled)
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_opt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid_a",
        "auto_opt == 0 || auto_opt == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded_c",
        "auto_opt >= 0 && auto_opt <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "boolean auto-stroke optimization flag is 0 or 1");
}
