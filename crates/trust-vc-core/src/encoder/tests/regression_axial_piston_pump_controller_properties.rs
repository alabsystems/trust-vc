// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: axial piston pump controller properties

use super::*;

#[test]
fn test_displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("displacement_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "displacement_x10 >= 10 && displacement_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "displacement_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "displacement_x10 >= 10 && displacement_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "displacement x10 cc/rev bounded 10-5000 (100.0 cc/rev)",
    );
}

#[test]
fn test_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "max_pressure >= 100 && max_pressure <= 700",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "max_pressure == 350"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "max_pressure >= 100 && max_pressure <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure bar bounded 100-700");
}

#[test]
fn test_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "speed >= 500 && speed <= 4000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "speed == 1800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "speed >= 500 && speed <= 4000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed RPM bounded 500-4000");
}

#[test]
fn test_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "flow_rate_x10 >= 10 && flow_rate_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "flow_rate_x10 == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "flow_rate_x10 >= 10 && flow_rate_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 L/min bounded 10-5000 (150.0 L/min)");
}

#[test]
fn test_efficiency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("efficiency_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "efficiency_x10 >= 700 && efficiency_x10 <= 980",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "efficiency_x10 == 920"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "efficiency_x10 >= 700 && efficiency_x10 <= 980",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "efficiency x10 percent bounded 700-980 (92.0%)");
}

#[test]
fn test_piston_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("piston_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "piston_count >= 5 && piston_count <= 11",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "piston_count == 9"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "piston_count >= 5 && piston_count <= 11",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "piston count bounded 5-11");
}

#[test]
fn test_swashplate_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("swashplate_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "swashplate_type == 1 || swashplate_type == 2 || swashplate_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "swashplate_type >= 1 && swashplate_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "swashplate type 1=fixed 2=variable 3=through-drive",
    );
}

#[test]
fn test_port_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "port_type == 1 || port_type == 2 || port_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "port_type >= 1 && port_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "port type 1=SAE 2=BSP 3=metric");
}

#[test]
fn test_control_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("control_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "control_type == 1 || control_type == 2 || control_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "control_type >= 1 && control_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "control type 1=pressure-compensated 2=load-sensing 3=electrohydraulic",
    );
}

#[test]
fn test_case_drain_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("case_drain", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "case_drain == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_true",
        "if case_drain == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "case drain flag boolean");
}
