// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_axial_pump_impeller_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "dia >= 100 && dia <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bounded",
        "dia >= 100 && dia <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller diameter bounded to 100-2000mm");
}

#[test]
fn test_axial_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow >= 100 && flow <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow >= 100 && flow <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate bounded to 100-500000 L/min");
}

#[test]
fn test_axial_pump_head_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "head_range",
        "head_x10 >= 5 && head_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "head_bounded",
        "head_x10 >= 5 && head_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "head x10 bounded to 5-300 (0.5-30.0 meters)");
}

#[test]
fn test_axial_pump_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("eff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "eff_range",
        "eff_x10 >= 500 && eff_x10 <= 950",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "eff_bounded",
        "eff_x10 >= 500 && eff_x10 <= 950",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency x10 bounded to 500-950 (50.0-95.0%)");
}

#[test]
fn test_axial_pump_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 100 && rpm <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 100 && rpm <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotational speed bounded to 100-3600 RPM");
}

#[test]
fn test_axial_pump_blade_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blades", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blade_range",
        "blades >= 2 && blades <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blade_bounded",
        "blades >= 2 && blades <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blade count bounded to 2-8");
}

#[test]
fn test_axial_pump_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_enum",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "material is cast iron (1), stainless steel (2), or bronze (3)",
    );
}

#[test]
fn test_axial_pump_orientation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("orient", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "orient_enum",
        "orient == 1 || orient == 2 || orient == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "orient_valid",
        "orient == 1 || orient == 2 || orient == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "orientation is horizontal (1), vertical (2), or inclined (3)",
    );
}

#[test]
fn test_axial_pump_sealing_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_enum",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "seal_valid",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sealing is mechanical seal (1), packing (2), or sealless (3)",
    );
}

#[test]
fn test_axial_pump_variable_pitch_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vp_bool", "vp == 0 || vp == 1"));
    ctx.push_obligation(ProofObligation::assert("vp_valid", "vp == 0 || vp == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "variable pitch flag is boolean (0 or 1)");
}
