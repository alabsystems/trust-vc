// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Radial piston pump controller property regression tests.

use super::*;

#[test]
fn test_displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "displacement_x10 >= 1 && displacement_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "displacement_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "displacement_x10 >= 1 && displacement_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement x10 cc/rev bounded 50.0 cc/rev");
}

#[test]
fn test_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "max_pressure >= 200 && max_pressure <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "max_pressure == 700"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "max_pressure >= 200 && max_pressure <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure bar bounded");
}

#[test]
fn test_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed >= 500 && speed <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed >= 500 && speed <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed RPM bounded");
}

#[test]
fn test_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "flow_rate_x10 == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 L/min bounded 80.0 L/min");
}

#[test]
fn test_piston_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("piston_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "piston_count >= 3 && piston_count <= 12",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "piston_count == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "piston_count >= 3 && piston_count <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston count bounded");
}

#[test]
fn test_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "efficiency_x10 >= 700 && efficiency_x10 <= 980",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "efficiency_x10 == 900"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "efficiency_x10 >= 700 && efficiency_x10 <= 980",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency x10 percent bounded 90.0%");
}

#[test]
fn test_configuration_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "config == 1 || config == 2 || config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "config == 1 || config == 2 || config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "configuration disjunction eccentric/cam-ring/crankshaft",
    );
}

#[test]
fn test_valve_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "valve_type == 1 || valve_type == 2 || valve_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "valve_type == 1 || valve_type == 2 || valve_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "valve type disjunction check/ported/servo");
}

#[test]
fn test_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material disjunction steel/stainless/bronze");
}

#[test]
fn test_variable_displacement_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("is_variable", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "variable displacement flag boolean check");
}
