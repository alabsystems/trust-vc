// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Flow rate is stored as x100 mL/min (500 = 5.00 mL/min).
/// Valid range: 1..=100000.
#[test]
fn test_tube_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_rate >= 1 && flow_rate <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_rate == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_rate >= 1 && flow_rate <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 500 (5.00 mL/min) within bounds");
}

/// Roller speed in RPM. Valid range: 1..=600.
#[test]
fn test_tube_pump_roller_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 1 && rpm <= 600",
    ));
    ctx.push_obligation(ProofObligation::assume("rpm_val", "rpm == 100"));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 1 && rpm <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "roller speed 100 RPM within bounds");
}

/// Tube inner diameter stored as x100 mm (160 = 1.60 mm).
/// Valid range: 10..=2500.
#[test]
fn test_tube_pump_tube_inner_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "diameter >= 10 && diameter <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assume("dia_val", "diameter == 160"));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bounded",
        "diameter >= 10 && diameter <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube inner diameter 160 (1.60 mm) within bounds");
}

/// Max pressure stored as x10 bar (30 = 3.0 bar).
/// Valid range: 1..=100.
#[test]
fn test_tube_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pres_range",
        "pressure >= 1 && pressure <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("pres_val", "pressure == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "pres_bounded",
        "pressure >= 1 && pressure <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 30 (3.0 bar) within bounds");
}

/// Number of rollers on the pump head. Valid range: 2..=12.
#[test]
fn test_tube_pump_number_of_rollers_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rollers", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "roller_range",
        "rollers >= 2 && rollers <= 12",
    ));
    ctx.push_obligation(ProofObligation::assume("roller_val", "rollers == 4"));
    ctx.push_obligation(ProofObligation::assert(
        "roller_bounded",
        "rollers >= 2 && rollers <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "4 rollers within bounds");
}

/// Tube wall thickness stored as x100 mm (80 = 0.80 mm).
/// Valid range: 10..=500.
#[test]
fn test_tube_pump_wall_thickness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thickness", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thick_range",
        "thickness >= 10 && thickness <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("thick_val", "thickness == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "thick_bounded",
        "thickness >= 10 && thickness <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wall thickness 80 (0.80 mm) within bounds");
}

/// Tube material encoded as: 1=silicone, 2=PharMed, 3=Viton.
#[test]
fn test_tube_pump_tube_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mat_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "silicone (1) is a valid tube material");
}

/// Pump head type: 1=fixed-occlusion, 2=adjustable-occlusion, 3=cartridge.
#[test]
fn test_tube_pump_head_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("head_val", "head_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "head_valid",
        "head_type == 1 || head_type == 2 || head_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "adjustable-occlusion (2) is a valid head type");
}

/// Drive mode: 1=continuous, 2=reversing, 3=pulsed-dose.
#[test]
fn test_tube_pump_drive_mode_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "drive_mode == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "drive_mode == 1 || drive_mode == 2 || drive_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "continuous (1) is a valid drive mode");
}

/// Automatic calibration flag: i32 boolean (1=enabled, 0=disabled).
/// When flag==1, calibration result must be 1.
#[test]
fn test_tube_pump_auto_calibration_enabled() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cal_flag", i32_ty());
    ctx.declare_var_typed("cal_result", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "cal_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "result_def",
        "cal_result == if cal_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cal_active", "cal_result == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "calibration enabled when flag is 1");
}
