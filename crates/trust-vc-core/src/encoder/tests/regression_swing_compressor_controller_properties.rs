// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_swing_compressor_discharge_pressure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range_a",
        "press_x10 >= 10 && press_x10 <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_range_c",
        "press_x10 >= 10 && press_x10 <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swing compressor discharge pressure at x10 bar");
}

#[test]
fn test_swing_compressor_motor_speed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range_a",
        "speed >= 1000 && speed <= 7000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_range_c",
        "speed >= 1000 && speed <= 7000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swing compressor motor speed in RPM");
}

#[test]
fn test_swing_compressor_displacement() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "displacement_range_a",
        "disp_x100 >= 50 && disp_x100 <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "displacement_range_c",
        "disp_x100 >= 50 && disp_x100 <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swing compressor displacement at x100 cc");
}

#[test]
fn test_swing_compressor_discharge_temperature() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_offset_range_a",
        "temp_off >= 120 && temp_off <= 380",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_offset_range_c",
        "temp_off >= 120 && temp_off <= 380",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "swing compressor discharge temperature offset +100 C",
    );
}

#[test]
fn test_swing_compressor_swing_angle() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "swing_angle_range_a",
        "angle_x10 >= 100 && angle_x10 <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "swing_angle_range_c",
        "angle_x10 >= 100 && angle_x10 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swing compressor swing angle at x10 degrees");
}

#[test]
fn test_swing_compressor_cop() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cop_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cop_range_a",
        "cop_x100 >= 100 && cop_x100 <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cop_range_c",
        "cop_x100 >= 100 && cop_x100 <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swing compressor COP at x100");
}

#[test]
fn test_swing_compressor_refrigerant() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrigerant", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "refrigerant_range_a",
        "refrigerant >= 1 && refrigerant <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "refrigerant_range_c",
        "refrigerant >= 1 && refrigerant <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swing compressor refrigerant 3-way selection");
}

#[test]
fn test_swing_compressor_vane_material() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vane_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vane_material_range_a",
        "vane_material >= 1 && vane_material <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vane_material_range_c",
        "vane_material >= 1 && vane_material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swing compressor vane material 3-way selection");
}

#[test]
fn test_swing_compressor_capacity_modulation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("modulation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "modulation_range_a",
        "modulation >= 1 && modulation <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "modulation_range_c",
        "modulation >= 1 && modulation <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "swing compressor capacity modulation 3-way selection",
    );
}

#[test]
fn test_swing_compressor_auto_defrost() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("defrost_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "defrost_bool_a",
        "defrost_flag >= 0 && defrost_flag <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "defrost_bool_c",
        "defrost_flag >= 0 && defrost_flag <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "swing compressor auto defrost boolean control flag",
    );
}
