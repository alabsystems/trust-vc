// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates <andrewyates.name@gmail.com>
// Regression tests: hydraulic ram pump controller properties

use super::*;

#[test]
fn test_drive_pipe_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_pipe_length", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "drive_pipe_length >= 5 && drive_pipe_length <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "drive_pipe_length == 30"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "drive_pipe_length >= 5 && drive_pipe_length <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive pipe length m bounded 5-100");
}

#[test]
fn test_delivery_head_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("delivery_head", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "delivery_head >= 5 && delivery_head <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "delivery_head == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "delivery_head >= 5 && delivery_head <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "delivery head m bounded 5-200");
}

#[test]
fn test_supply_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("supply_flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "supply_flow_x10 >= 10 && supply_flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "supply_flow_x10 == 800"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "supply_flow_x10 >= 10 && supply_flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "supply flow x10 L/min bounded 10-5000 (80.0 L/min)",
    );
}

#[test]
fn test_cycle_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "cycle_rate >= 20 && cycle_rate <= 150",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "cycle_rate == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "cycle_rate >= 20 && cycle_rate <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle rate cycles/min bounded 20-150");
}

#[test]
fn test_delivery_flow_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("delivery_flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "delivery_flow_x10 >= 1 && delivery_flow_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "delivery_flow_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "delivery_flow_x10 >= 1 && delivery_flow_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "delivery flow x10 L/min bounded 1-1000 (15.0 L/min)",
    );
}

#[test]
fn test_waste_valve_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("waste_valve_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "waste_valve_type == 1 || waste_valve_type == 2 || waste_valve_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "waste_valve_type >= 1 && waste_valve_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "waste valve type 1=spring-loaded 2=weight-loaded 3=hydraulic-pilot",
    );
}

#[test]
fn test_air_chamber_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_chamber_material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "air_chamber_material == 1 || air_chamber_material == 2 || air_chamber_material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "air_chamber_material >= 1 && air_chamber_material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air chamber material 1=cast-iron 2=stainless 3=bronze",
    );
}

#[test]
fn test_check_valve_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("check_valve_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "check_valve_type == 1 || check_valve_type == 2 || check_valve_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "check_valve_type >= 1 && check_valve_type <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "check valve type 1=swing 2=disc 3=ball");
}

#[test]
fn test_drive_pipe_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_pipe_diameter_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "drive_pipe_diameter_x10 >= 20 && drive_pipe_diameter_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "val",
        "drive_pipe_diameter_x10 == 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "drive_pipe_diameter_x10 >= 20 && drive_pipe_diameter_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive pipe diameter x10 mm bounded 20-2000 (50.0 mm)",
    );
}

#[test]
fn test_auto_start_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_start", i32_ty());
    ctx.push_obligation(ProofObligation::assume("val", "auto_start == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_true",
        "if auto_start == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto start flag boolean");
}
