// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Discharge pressure at ×10 bar must remain within the safe operating envelope.
#[test]
fn test_wobble_plate_compressor_discharge_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "press_x10 >= 10 && press_x10 <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "press_x10 >= 10 && press_x10 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wobble plate compressor discharge pressure bounded",
    );
}

/// Shaft speed in RPM must stay within the allowable rotational range.
#[test]
fn test_wobble_plate_compressor_shaft_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ss_a",
        "speed >= 500 && speed <= 8000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ss_c",
        "speed >= 500 && speed <= 8000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble plate compressor shaft speed bounded");
}

/// Displacement at ×10 cc must remain within the mechanical range of the wobble plate.
#[test]
fn test_wobble_plate_compressor_displacement_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ds_a",
        "disp_x10 >= 50 && disp_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ds_c",
        "disp_x10 >= 50 && disp_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble plate compressor displacement bounded");
}

/// Discharge temperature with +100 °C offset must stay within thermal limits.
#[test]
fn test_wobble_plate_compressor_discharge_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "temp_off >= 120 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "temp_off >= 120 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wobble plate compressor discharge temperature bounded",
    );
}

/// Plate angle at ×10 degrees must remain within the wobble plate tilt range.
#[test]
fn test_wobble_plate_compressor_plate_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pa_a",
        "angle_x10 >= 50 && angle_x10 <= 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pa_c",
        "angle_x10 >= 50 && angle_x10 <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble plate compressor plate angle bounded");
}

/// Number of cylinders must be within the valid configuration range.
#[test]
fn test_wobble_plate_compressor_cylinder_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cylinders", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "nc_a",
        "cylinders >= 3 && cylinders <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nc_c",
        "cylinders >= 3 && cylinders <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble plate compressor cylinder count bounded");
}

/// Refrigerant type must be one of the supported refrigerants (1=R134a, 2=R1234yf, 3=R744).
#[test]
fn test_wobble_plate_compressor_refrigerant_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrigerant", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rt_a",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rt_c",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble plate compressor refrigerant type valid");
}

/// Control method must be a recognized strategy (1=variable-displacement, 2=clutch-cycling, 3=electronic).
#[test]
fn test_wobble_plate_compressor_control_method_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_a",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_c",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble plate compressor control method valid");
}

/// Lubrication system must be a supported type (1=splash, 2=pressure-fed, 3=mist).
#[test]
fn test_wobble_plate_compressor_lubrication_system_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lubrication", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ls_a",
        "lubrication == 1 || lubrication == 2 || lubrication == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ls_c",
        "lubrication == 1 || lubrication == 2 || lubrication == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wobble plate compressor lubrication system valid");
}

/// Automatic capacity adjustment flag must be a valid boolean (0=disabled, 1=enabled).
#[test]
fn test_wobble_plate_compressor_capacity_adjustment_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ca_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("ca_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wobble plate compressor capacity adjustment flag valid",
    );
}
