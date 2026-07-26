// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial paddle dryer property verification.
// Encodes key parameters of an industrial paddle dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Drying capacity (kg/h) — throughput bounded [10, 5000], value 500.
#[test]
fn test_drying_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_kgh", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity_kgh == 500"));
    ctx.push_obligation(ProofObligation::assert("cap_min", "capacity_kgh >= 10"));
    ctx.push_obligation(ProofObligation::assert("cap_max", "capacity_kgh <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying capacity 500 kg/h in [10, 5000]");
}

/// Test 2: Heat transfer area (x10 m²) — scaled area bounded [10, 1000].
/// 200 represents 20.0 m². Value 200 (20.0 m² heat transfer area).
#[test]
fn test_heat_transfer_area_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("area_val", "area_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert("area_min", "area_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("area_max", "area_x10 <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heat transfer area 20.0 m2 (200 x10) in [10, 1000]",
    );
}

/// Test 3: Jacket temperature (deg C) — heating jacket bounded [80, 300], value 180.
#[test]
fn test_jacket_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("jt_val", "jacket_temp == 180"));
    ctx.push_obligation(ProofObligation::assert("jt_min", "jacket_temp >= 80"));
    ctx.push_obligation(ProofObligation::assert("jt_max", "jacket_temp <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jacket temperature 180 C in [80, 300]");
}

/// Test 4: Dryer type — 3-way disjunction.
/// 1=single shaft, 2=twin shaft, 3=four shaft. Value 2 (twin shaft).
#[test]
fn test_dryer_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dryer_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dtype_val", "dryer_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_dryer",
        "dryer_type == 1 || dryer_type == 2 || dryer_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dryer type 2 (twin shaft) is valid 3-way disjunction",
    );
}

/// Test 5: Heating medium — 3-way disjunction.
/// 1=steam, 2=hot oil, 3=hot water. Value 1 (steam).
#[test]
fn test_heating_medium_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_medium", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hm_val", "heat_medium == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_medium",
        "heat_medium == 1 || heat_medium == 2 || heat_medium == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating medium 1 (steam) is valid 3-way disjunction",
    );
}

/// Test 6: Paddle speed (RPM) — rotational speed bounded [2, 50], value 15.
#[test]
fn test_paddle_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_rpm == 15"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_rpm >= 2"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_rpm <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paddle speed 15 RPM in [2, 50]");
}

/// Test 7: Residence time (min) — material dwell time bounded [5, 300], value 60.
#[test]
fn test_residence_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_time", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rt_val", "res_time == 60"));
    ctx.push_obligation(ProofObligation::assert("rt_min", "res_time >= 5"));
    ctx.push_obligation(ProofObligation::assert("rt_max", "res_time <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time 60 min in [5, 300]");
}

/// Test 8: Vapor handling — 3-way disjunction.
/// 1=atmospheric, 2=vacuum, 3=inert gas. Value 2 (vacuum).
#[test]
fn test_vapor_handling_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vapor_mode", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vm_val", "vapor_mode == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_vapor",
        "vapor_mode == 1 || vapor_mode == 2 || vapor_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vapor handling 2 (vacuum) is valid 3-way disjunction",
    );
}

/// Test 9: Fill level (x10 %) — dryer fill as scaled percentage bounded [300, 800].
/// 600 represents 60.0%. Value 600 (60.0% fill level).
#[test]
fn test_fill_level_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fill_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fill_val", "fill_x10 == 600"));
    ctx.push_obligation(ProofObligation::assert("fill_min", "fill_x10 >= 300"));
    ctx.push_obligation(ProofObligation::assert("fill_max", "fill_x10 <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fill level 60.0% (600 x10) in [300, 800]");
}

/// Test 10: Dust filter — boolean flag using i32 with if/else pattern.
/// Flag 1 = dust filter installed, which activates filtration (filter_active = 1).
#[test]
fn test_dust_filter_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dust_filter_flag", i32_ty());
    ctx.declare_var_typed("filter_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "dust_filter_flag == 0 || dust_filter_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "dust_filter_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "filter_def",
        "filter_active == if dust_filter_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("filter_on", "filter_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dust filter flag activates filtration");
}
