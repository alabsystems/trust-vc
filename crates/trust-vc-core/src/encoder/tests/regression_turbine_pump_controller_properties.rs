// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests for turbine pump controller verification properties.

use super::*;

#[test]
fn test_turbine_pump_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_rate_x10_range",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "flow_rate_x10_val",
        "flow_rate_x10 == 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_rate_x10_bounded",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "delivery flow rate x10 (200.0 m3/h) within bounds");
}

#[test]
fn test_turbine_pump_head_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("head", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "head_range",
        "head >= 10 && head <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("head_val", "head == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "head_bounded",
        "head >= 10 && head <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "total head in meters within bounds");
}

#[test]
fn test_turbine_pump_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "efficiency_x10_range",
        "efficiency_x10 >= 300 && efficiency_x10 <= 950",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "efficiency_x10_val",
        "efficiency_x10 == 850",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "efficiency_x10_bounded",
        "efficiency_x10 >= 300 && efficiency_x10 <= 950",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pump efficiency x10 (85.0%) within bounds");
}

#[test]
fn test_turbine_pump_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 500 && speed <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 1800"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 500 && speed <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "RPM within bounds");
}

#[test]
fn test_turbine_pump_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stages_range",
        "stages >= 1 && stages <= 20",
    ));
    ctx.push_obligation(ProofObligation::assume("stages_val", "stages == 6"));
    ctx.push_obligation(ProofObligation::assert(
        "stages_bounded",
        "stages >= 1 && stages <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of stages within bounds");
}

#[test]
fn test_turbine_pump_bowl_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bowl_diameter", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bowl_diameter_range",
        "bowl_diameter >= 100 && bowl_diameter <= 600",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "bowl_diameter_val",
        "bowl_diameter == 250",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bowl_diameter_bounded",
        "bowl_diameter >= 100 && bowl_diameter <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl diameter in mm within bounds");
}

#[test]
fn test_turbine_pump_impeller_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "impeller_type_val",
        "impeller_type == 1 || impeller_type == 2 || impeller_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "impeller_type_bounded",
        "impeller_type >= 1 && impeller_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller type (1=enclosed, 2=semi-open, 3=mixed-flow) within range",
    );
}

#[test]
fn test_turbine_pump_column_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("column_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "column_material_val",
        "column_material == 1 || column_material == 2 || column_material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "column_material_bounded",
        "column_material >= 1 && column_material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "column material (1=carbon-steel, 2=stainless, 3=fiberglass) within range",
    );
}

#[test]
fn test_turbine_pump_thrust_bearing_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thrust_bearing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thrust_bearing_val",
        "thrust_bearing == 1 || thrust_bearing == 2 || thrust_bearing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thrust_bearing_bounded",
        "thrust_bearing >= 1 && thrust_bearing <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "thrust bearing (1=oil-lubricated, 2=water-lubricated, 3=grease) within range",
    );
}

#[test]
fn test_turbine_pump_variable_speed_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("variable_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "variable_speed_val",
        "variable_speed == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "variable_speed_active",
        "if variable_speed == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "variable speed drive flag is active");
}
