// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Swash plate pump displacement in tenths of cc/rev (500 = 50.0 cc/rev).
/// Valid range: 10..=5000.
#[test]
fn test_swash_plate_pump_displacement_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "displacement >= 10 && displacement <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("disp_val", "displacement == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "disp_check",
        "displacement >= 10 && displacement <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement 500 (50.0 cc/rev) in valid range");
}

/// Maximum operating pressure in bar.
/// Valid range: 50..=500.
#[test]
fn test_swash_plate_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "max_pressure >= 50 && max_pressure <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("press_val", "max_pressure == 350"));
    ctx.push_obligation(ProofObligation::assert(
        "press_check",
        "max_pressure >= 50 && max_pressure <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 350 bar in valid range");
}

/// Maximum shaft speed in RPM.
/// Valid range: 500..=5000.
#[test]
fn test_swash_plate_pump_max_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "max_speed >= 500 && max_speed <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "max_speed == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "max_speed >= 500 && max_speed <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max speed 3000 RPM in valid range");
}

/// Swash plate angle in tenths of degrees (180 = 18.0 degrees).
/// Valid range: 10..=250.
#[test]
fn test_swash_plate_pump_swash_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("swash_angle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "angle_range",
        "swash_angle >= 10 && swash_angle <= 250",
    ));
    ctx.push_obligation(ProofObligation::assume("angle_val", "swash_angle == 180"));
    ctx.push_obligation(ProofObligation::assert(
        "angle_check",
        "swash_angle >= 10 && swash_angle <= 250",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "swash plate angle 180 (18.0 deg) in valid range");
}

/// Number of pistons in the rotating cylinder block.
/// Valid range: 5..=11 (odd numbers typical, but even permitted).
#[test]
fn test_swash_plate_pump_piston_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_pistons", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "piston_range",
        "num_pistons >= 5 && num_pistons <= 11",
    ));
    ctx.push_obligation(ProofObligation::assume("piston_val", "num_pistons == 9"));
    ctx.push_obligation(ProofObligation::assert(
        "piston_check",
        "num_pistons >= 5 && num_pistons <= 11",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "9 pistons in valid range");
}

/// Volumetric efficiency in tenths of percent (950 = 95.0%).
/// Valid range: 800..=1000 (80.0%..=100.0%).
#[test]
fn test_swash_plate_pump_volumetric_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol_eff", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "vol_eff >= 800 && vol_eff <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("eff_val", "vol_eff == 950"));
    ctx.push_obligation(ProofObligation::assert(
        "eff_check",
        "vol_eff >= 800 && vol_eff <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "volumetric efficiency 950 (95.0%) in valid range");
}

/// Control type enumeration:
///   1 = pressure-compensated
///   2 = load-sensing
///   3 = electro-hydraulic
#[test]
fn test_swash_plate_pump_control_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("control_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ctrl_val", "control_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "ctrl_check",
        "control_type == 1 || control_type == 2 || control_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "load-sensing control (2) is a valid control type");
}

/// Valve plate design enumeration:
///   1 = kidney-port
///   2 = slot-port
///   3 = spherical
#[test]
fn test_swash_plate_pump_valve_plate_design_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_plate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vp_val", "valve_plate == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "vp_check",
        "valve_plate == 1 || valve_plate == 2 || valve_plate == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "kidney-port valve plate (1) is a valid design");
}

/// Piston material enumeration:
///   1 = steel
///   2 = bronze
///   3 = ceramic-coated
#[test]
fn test_swash_plate_pump_piston_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("piston_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "piston_mat == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "piston_mat == 1 || piston_mat == 2 || piston_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "steel piston material (1) is a valid material");
}

/// Automatic displacement adjustment flag.
/// When flag == 1, the controller actively adjusts swash plate angle.
#[test]
fn test_swash_plate_pump_auto_displacement_adjustment() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_adjust", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_adjust == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "adjust_active",
        "(if auto_adjust == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto displacement adjustment active when flag is 1",
    );
}
