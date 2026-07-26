// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_plunger_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume("pressure_val", "pressure == 1500"));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_bounded",
        "pressure >= 50 && pressure <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max pressure 1500 bar within [50, 3000]");
}

#[test]
fn test_plunger_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_x10 == 250"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 250 (25.0 L/min x10) within [1, 5000]");
}

#[test]
fn test_plunger_pump_plunger_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diameter_val",
        "diameter_x10 == 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diameter_bounded",
        "diameter_x10 >= 10 && diameter_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plunger diameter 200 (20.0 mm x10) within [10, 1000]",
    );
}

#[test]
fn test_plunger_pump_stroke_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rate_val", "stroke_rate == 300"));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "stroke_rate >= 10 && stroke_rate <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stroke rate 300 strokes/min within [10, 600]");
}

#[test]
fn test_plunger_pump_number_of_plungers_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_plungers", i32_ty());
    ctx.push_obligation(ProofObligation::assume("plungers_val", "num_plungers == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "plungers_bounded",
        "num_plungers >= 1 && num_plungers <= 7",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of plungers 3 within [1, 7]");
}

#[test]
fn test_plunger_pump_packing_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("packing", i32_ty());
    ctx.push_obligation(ProofObligation::assume("packing_val", "packing == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "packing_valid",
        "packing == 1 || packing == 2 || packing == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "packing material 1 (PTFE) is one of PTFE/graphite/aramid",
    );
}

#[test]
fn test_plunger_pump_drive_mechanism_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", i32_ty());
    ctx.push_obligation(ProofObligation::assume("drive_val", "drive == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "drive_valid",
        "drive == 1 || drive == 2 || drive == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive mechanism 2 (cam) is one of crankshaft/cam/hydraulic",
    );
}

#[test]
fn test_plunger_pump_valve_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve", i32_ty());
    ctx.push_obligation(ProofObligation::assume("valve_val", "valve == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valve_valid",
        "valve == 1 || valve == 2 || valve == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "valve type 3 (disc) is one of ball/poppet/disc");
}

#[test]
fn test_plunger_pump_stroke_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("stroke_val", "stroke_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_bounded",
        "stroke_x10 >= 10 && stroke_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stroke length 500 (50.0 mm x10) within [10, 2000]");
}

#[test]
fn test_plunger_pump_pulsation_dampener_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "dampener_enabled",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pulsation dampener flag=1 means dampener is enabled",
    );
}
