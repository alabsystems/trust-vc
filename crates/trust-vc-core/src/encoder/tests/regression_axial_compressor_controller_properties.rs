// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_axial_compressor_shaft_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shaft_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shaft_speed_range",
        "shaft_speed >= 3000 && shaft_speed <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shaft_speed_bounded",
        "shaft_speed >= 3000 && shaft_speed <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shaft speed must be between 3000 and 20000 RPM");
}

#[test]
fn test_axial_compressor_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 1 && stages <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stages_bounded",
        "stages >= 1 && stages <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of stages must be between 1 and 20");
}

#[test]
fn test_axial_compressor_pressure_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_ratio_x10_range",
        "pressure_ratio_x10 >= 10 && pressure_ratio_x10 <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_ratio_x10_bounded",
        "pressure_ratio_x10 >= 10 && pressure_ratio_x10 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pressure ratio x10 must be between 10 and 400 representing 1.0 to 40.0",
    );
}

#[test]
fn test_axial_compressor_inlet_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_offset100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_temp_offset100_range",
        "inlet_temp_offset100 >= 50 && inlet_temp_offset100 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_temp_offset100_bounded",
        "inlet_temp_offset100 >= 50 && inlet_temp_offset100 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inlet temperature offset+100 must be between 50 and 200 representing -50C to 100C",
    );
}

#[test]
fn test_axial_compressor_mass_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass_flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mass_flow_range",
        "mass_flow >= 10 && mass_flow <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mass_flow_bounded",
        "mass_flow >= 10 && mass_flow <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass flow rate must be between 10 and 50000 kg/h");
}

#[test]
fn test_axial_compressor_surge_margin_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("surge_margin_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "surge_margin_x10_range",
        "surge_margin_x10 >= 50 && surge_margin_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "surge_margin_x10_bounded",
        "surge_margin_x10 >= 50 && surge_margin_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "surge margin x10 must be between 50 and 300 representing 5.0 to 30.0 percent",
    );
}

#[test]
fn test_axial_compressor_blade_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blade_material_range",
        "blade_material >= 1 && blade_material <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blade_material_valid",
        "blade_material >= 1 && blade_material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade material must be 1=titanium 2=nickel-alloy or 3=stainless-steel",
    );
}

#[test]
fn test_axial_compressor_control_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("control_method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "control_method_range",
        "control_method >= 1 && control_method <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "control_method_valid",
        "control_method >= 1 && control_method <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "control method must be 1=variable-IGV 2=variable-speed or 3=bleed-valve",
    );
}

#[test]
fn test_axial_compressor_sealing_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sealing_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sealing_type_range",
        "sealing_type >= 1 && sealing_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sealing_type_valid",
        "sealing_type >= 1 && sealing_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sealing type must be 1=labyrinth 2=brush or 3=dry-gas",
    );
}

#[test]
fn test_axial_compressor_auto_surge_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_surge_protection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_surge_protection_range",
        "auto_surge_protection >= 0 && auto_surge_protection <= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_surge_protection_valid",
        "auto_surge_protection >= 0 && auto_surge_protection <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto surge protection flag must be 0=disabled or 1=enabled",
    );
}
