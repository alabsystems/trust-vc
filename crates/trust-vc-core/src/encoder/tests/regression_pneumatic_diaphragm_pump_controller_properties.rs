// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 1 && flow_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_x10 == 1000"));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate x10 of 1000 (100.0 L/min) is within [1, 10000]",
    );
}

#[test]
fn test_max_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("press_val", "press_x10 == 70"));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 10 && press_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 of 70 (7.0 bar) is within [10, 100]",
    );
}

#[test]
fn test_air_consumption_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "air_range",
        "air_x10 >= 1 && air_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("air_val", "air_x10 == 80"));
    ctx.push_obligation(ProofObligation::assert(
        "air_bounded",
        "air_x10 >= 1 && air_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air consumption x10 of 80 (8.0 m3/min) is within [1, 500]",
    );
}

#[test]
fn test_suction_lift_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lift_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lift_range",
        "lift_x10 >= 10 && lift_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assume("lift_val", "lift_x10 == 60"));
    ctx.push_obligation(ProofObligation::assert(
        "lift_bounded",
        "lift_x10 >= 10 && lift_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suction lift x10 of 60 (6.0 m) is within [10, 100]",
    );
}

#[test]
fn test_port_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("port", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "port_range",
        "port >= 6 && port <= 150",
    ));
    ctx.push_obligation(ProofObligation::assume("port_val", "port == 50"));
    ctx.push_obligation(ProofObligation::assert(
        "port_bounded",
        "port >= 6 && port <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "port size 50 mm is within [6, 150]");
}

#[test]
fn test_stroke_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("strokes", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stroke_range",
        "strokes >= 10 && strokes <= 500",
    ));
    ctx.push_obligation(ProofObligation::assume("stroke_val", "strokes == 120"));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_bounded",
        "strokes >= 10 && strokes <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stroke count 120 cycles/min is within [10, 500]");
}

#[test]
fn test_diaphragm_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_material",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_in_range",
        "material >= 1 && material <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "diaphragm material (1=PTFE, 2=Buna-N, 3=Santoprene) is valid",
    );
}

#[test]
fn test_housing_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("housing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_housing",
        "housing == 1 || housing == 2 || housing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "housing_in_range",
        "housing >= 1 && housing <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "housing material (1=aluminum, 2=stainless, 3=polypropylene) is valid",
    );
}

#[test]
fn test_valve_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_valve",
        "valve == 1 || valve == 2 || valve == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valve_in_range",
        "valve >= 1 && valve <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "valve type (1=ball, 2=flap, 3=diaphragm) is valid");
}

#[test]
fn test_deadhead_safe_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("safe", i32_ty());
    ctx.push_obligation(ProofObligation::assume("safe_is_true", "safe == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "deadhead_safe",
        "if safe == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "deadhead safe flag asserts true when safe == 1");
}
