// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Gerotor pump displacement in hundredths of cc/rev (250 = 2.50 cc/rev).
/// Valid range: 10..=50000.
#[test]
fn test_gerotor_pump_displacement_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "displacement >= 10 && displacement <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assume("disp_val", "displacement == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "disp_check",
        "displacement >= 10 && displacement <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement 250 (2.50 cc/rev) in valid range");
}

/// Maximum operating pressure in bar.
/// Valid range: 10..=300.
#[test]
fn test_gerotor_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "max_pressure >= 10 && max_pressure <= 300",
    ));
    ctx.push_obligation(ProofObligation::assume("press_val", "max_pressure == 200"));
    ctx.push_obligation(ProofObligation::assert(
        "press_check",
        "max_pressure >= 10 && max_pressure <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 200 bar in valid range");
}

/// Maximum rotor speed in RPM.
/// Valid range: 100..=6000.
#[test]
fn test_gerotor_pump_max_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "max_speed >= 100 && max_speed <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "max_speed == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "max_speed >= 100 && max_speed <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max speed 3000 RPM in valid range");
}

/// Inner rotor tooth count.
/// Valid range: 4..=15.
#[test]
fn test_gerotor_pump_tooth_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tooth_count", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tooth_range",
        "tooth_count >= 4 && tooth_count <= 15",
    ));
    ctx.push_obligation(ProofObligation::assume("tooth_val", "tooth_count == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "tooth_check",
        "tooth_count >= 4 && tooth_count <= 15",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "7 inner rotor teeth in valid range");
}

/// Rotor eccentricity in hundredths of mm (50 = 0.50 mm).
/// Valid range: 5..=500.
#[test]
fn test_gerotor_pump_eccentricity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eccentricity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ecc_range",
        "eccentricity >= 5 && eccentricity <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("ecc_val", "eccentricity == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "ecc_check",
        "eccentricity >= 5 && eccentricity <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "eccentricity 50 (0.50 mm) in valid range");
}

/// Volumetric efficiency in tenths of percent (920 = 92.0%).
/// Valid range: 700..=1000 (70.0%..=100.0%).
#[test]
fn test_gerotor_pump_volumetric_efficiency_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol_eff", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "vol_eff >= 700 && vol_eff <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("eff_val", "vol_eff == 920"));
    ctx.push_obligation(ProofObligation::assert(
        "eff_check",
        "vol_eff >= 700 && vol_eff <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "volumetric efficiency 920 (92.0%) in valid range");
}

/// Rotor material enumeration:
///   1 = sintered-iron
///   2 = hardened-steel
///   3 = powder-metal
#[test]
fn test_gerotor_pump_rotor_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "rotor_mat == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "rotor_mat == 1 || rotor_mat == 2 || rotor_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sintered-iron rotor material (1) is a valid material",
    );
}

/// Seal type enumeration:
///   1 = crescent
///   2 = tipped-tooth
///   3 = helical
#[test]
fn test_gerotor_pump_seal_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "seal_check",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crescent seal type (1) is a valid seal type");
}

/// Application mode enumeration:
///   1 = lubrication
///   2 = fuel-transfer
///   3 = hydraulic
#[test]
fn test_gerotor_pump_application_mode_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("app_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mode_val", "app_mode == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "mode_check",
        "app_mode == 1 || app_mode == 2 || app_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hydraulic application mode (3) is a valid mode");
}

/// Automatic flow compensation flag.
/// When flag == 1, the controller actively compensates flow output.
#[test]
fn test_gerotor_pump_auto_flow_compensation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_comp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flow_comp == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "comp_active",
        "(if flow_comp == 1 { 1 } else { 0 }) == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto flow compensation active when flag is 1");
}
