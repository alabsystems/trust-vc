// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Bent axis pump displacement in tenths of cc/rev (750 = 75.0 cc/rev).
/// Valid range: 10..=10000.
#[test]
fn test_bent_axis_pump_displacement_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "displacement >= 10 && displacement <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("disp_val", "displacement == 750"));
    ctx.push_obligation(ProofObligation::assert(
        "disp_check",
        "displacement >= 10 && displacement <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement 750 (75.0 cc/rev) in valid range");
}

/// Maximum operating pressure in bar.
/// Valid range: 100..=500.
#[test]
fn test_bent_axis_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "max_pressure >= 100 && max_pressure <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("press_val", "max_pressure == 400"));
    ctx.push_obligation(ProofObligation::assert(
        "press_check",
        "max_pressure >= 100 && max_pressure <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 400 bar in valid range");
}

/// Maximum shaft speed in RPM.
/// Valid range: 500..=6000.
#[test]
fn test_bent_axis_pump_max_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "max_speed >= 500 && max_speed <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "max_speed == 4000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "max_speed >= 500 && max_speed <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max speed 4000 RPM in valid range");
}

/// Bend angle in tenths of degrees (250 = 25.0 degrees).
/// Valid range: 50..=400 (5.0..=40.0 degrees).
#[test]
fn test_bent_axis_pump_bend_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bend_angle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_range",
        "bend_angle >= 50 && bend_angle <= 400",
    ));
    ctx.push_obligation(ProofObligation::assume("angle_val", "bend_angle == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "angle_check",
        "bend_angle >= 50 && bend_angle <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bend angle 250 (25.0 deg) in valid range");
}

/// Number of pistons in the rotating cylinder block.
/// Valid range: 5..=11.
#[test]
fn test_bent_axis_pump_piston_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_pistons", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "piston_range",
        "num_pistons >= 5 && num_pistons <= 11",
    ));
    ctx.push_obligation(ProofObligation::assume("piston_val", "num_pistons == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "piston_check",
        "num_pistons >= 5 && num_pistons <= 11",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 pistons in valid range");
}

/// Mechanical efficiency in tenths of percent (960 = 96.0%).
/// Valid range: 800..=1000 (80.0%..=100.0%).
#[test]
fn test_bent_axis_pump_mechanical_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mech_eff", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "mech_eff >= 800 && mech_eff <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("eff_val", "mech_eff == 960"));
    ctx.push_obligation(ProofObligation::assert(
        "eff_check",
        "mech_eff >= 800 && mech_eff <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mechanical efficiency 960 (96.0%) in valid range");
}

/// Drive coupling enumeration:
///   1 = spline
///   2 = keyed-shaft
///   3 = universal-joint
#[test]
fn test_bent_axis_pump_drive_coupling_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_coupling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "coupling_val",
        "drive_coupling == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "coupling_check",
        "drive_coupling == 1 || drive_coupling == 2 || drive_coupling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "spline drive coupling (1) is a valid coupling type",
    );
}

/// Housing material enumeration:
///   1 = cast-iron
///   2 = aluminum
///   3 = ductile-iron
#[test]
fn test_bent_axis_pump_housing_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("housing_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "housing_mat == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "housing_mat == 1 || housing_mat == 2 || housing_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cast-iron housing material (1) is a valid material",
    );
}

/// Sealing system enumeration:
///   1 = lip-seal
///   2 = mechanical-seal
///   3 = labyrinth
#[test]
fn test_bent_axis_pump_sealing_system_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "seal_check",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "mechanical-seal sealing system (2) is a valid seal type",
    );
}

/// Automatic angle adjustment flag.
/// When flag == 1, the controller actively adjusts the bent axis angle.
#[test]
fn test_bent_axis_pump_auto_angle_adjustment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_adjust", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_adjust == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "adjust_active",
        "(if auto_adjust == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto angle adjustment active when flag is 1");
}
