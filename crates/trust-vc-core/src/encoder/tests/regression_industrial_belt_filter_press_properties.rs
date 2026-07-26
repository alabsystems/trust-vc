// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial belt filter press property verification.
// Encodes key parameters of an industrial belt filter press and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Belt width (mm) — bounded [500, 3000].
#[test]
fn test_belt_filter_belt_width_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bw", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bw_range",
        "bw >= 500 && bw <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bw_check",
        "bw >= 500 && bw <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt width bounded [500, 3000] mm");
}

/// Test 2: Belt speed x10 (m/min, 0.1 resolution) — bounded [5, 300].
#[test]
fn test_belt_filter_belt_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spd_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spd_range",
        "spd_x10 >= 5 && spd_x10 <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spd_check",
        "spd_x10 >= 5 && spd_x10 <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt speed x10 bounded [5, 300]");
}

/// Test 3: Squeeze pressure x10 (bar, 0.1 resolution) — bounded [10, 200].
#[test]
fn test_belt_filter_squeeze_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_check",
        "press_x10 >= 10 && press_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "squeeze pressure x10 bounded [10, 200]");
}

/// Test 4: Cake thickness x10 (mm, 0.1 resolution) — bounded [10, 500].
#[test]
fn test_belt_filter_cake_thickness_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cake_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cake_range",
        "cake_x10 >= 10 && cake_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cake_check",
        "cake_x10 >= 10 && cake_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cake thickness x10 bounded [10, 500]");
}

/// Test 5: Filtrate flow (L/min) — bounded [10, 5000].
#[test]
fn test_belt_filter_filtrate_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow >= 10 && flow <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_check",
        "flow >= 10 && flow <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filtrate flow bounded [10, 5000] L/min");
}

/// Test 6: Wash water ratio x10 (0.1 resolution) — bounded [5, 100].
#[test]
fn test_belt_filter_wash_water_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_range",
        "ratio_x10 >= 5 && ratio_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_check",
        "ratio_x10 >= 5 && ratio_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wash water ratio x10 bounded [5, 100]");
}

/// Test 7: Belt material — 3-way disjunction (1=polyester, 2=polypropylene, 3=nylon).
#[test]
fn test_belt_filter_belt_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_domain",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt material is valid 3-way disjunction");
}

/// Test 8: Dewatering zone — 3-way disjunction (1=gravity, 2=wedge, 3=pressure).
#[test]
fn test_belt_filter_dewatering_zone_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zone", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "zone_domain",
        "zone == 1 || zone == 2 || zone == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "zone_check",
        "zone == 1 || zone == 2 || zone == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dewatering zone is valid 3-way disjunction");
}

/// Test 9: Discharge method — 3-way disjunction (1=scraper, 2=air blast, 3=roller).
#[test]
fn test_belt_filter_discharge_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dis_domain",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dis_check",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge method is valid 3-way disjunction");
}

/// Test 10: Belt tracking flag — boolean (0 or 1).
#[test]
fn test_belt_filter_belt_tracking_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trk", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "trk_domain",
        "trk == 0 || trk == 1",
    ));
    ctx.push_obligation(ProofObligation::assert("trk_check", "trk == 0 || trk == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt tracking flag is boolean (0 or 1)");
}
