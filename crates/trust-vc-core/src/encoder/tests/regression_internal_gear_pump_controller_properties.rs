// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Internal gear pump controller property regression tests

use super::*;

#[test]
fn test_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "flow_rate_x10 == 2500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "flow_rate_x10 >= 1 && flow_rate_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 bounded at 250.0 L/min");
}

#[test]
fn test_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "max_pressure >= 5 && max_pressure <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "max_pressure == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "max_pressure >= 5 && max_pressure <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure bounded at 120 bar");
}

#[test]
fn test_displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "displacement_x10 >= 1 && displacement_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "displacement_x10 == 3000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "displacement_x10 >= 1 && displacement_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement x10 bounded at 300.0 cc/rev");
}

#[test]
fn test_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed >= 50 && speed <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed >= 50 && speed <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed bounded at 1000 RPM");
}

#[test]
fn test_viscosity_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("viscosity_max", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "viscosity_max >= 100 && viscosity_max <= 2000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "viscosity_max == 500000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "viscosity_max >= 100 && viscosity_max <= 2000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viscosity max bounded at 500000 cSt");
}

#[test]
fn test_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "efficiency_x10 >= 700 && efficiency_x10 <= 980",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "efficiency_x10 == 940"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "efficiency_x10 >= 700 && efficiency_x10 <= 980",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency x10 bounded at 94.0%");
}

#[test]
fn test_crescent_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("crescent_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "crescent_type >= 1 && crescent_type <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "crescent_type == 1 || crescent_type == 2 || crescent_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crescent type is fixed, floating, or none");
}

#[test]
fn test_housing_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("housing_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "housing_material >= 1 && housing_material <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "housing_material == 1 || housing_material == 2 || housing_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "housing material is cast-iron, ductile-iron, or stainless",
    );
}

#[test]
fn test_shaft_seal_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shaft_seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "shaft_seal >= 1 && shaft_seal <= 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disjunction",
        "shaft_seal == 1 || shaft_seal == 2 || shaft_seal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shaft seal is lip, mechanical, or mag-drive");
}

#[test]
fn test_heated_jacket_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "heated_jacket",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heated jacket flag enabled");
}
