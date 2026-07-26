// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial paddle dryer controller property verification.
// Encodes key controller parameters and verifies bounded, disjunctive,
// and boolean-flag constraints through the trust_vc verification pipeline.

/// Test 1: Vessel volume (L) bounded [50, 10000].
#[test]
fn test_paddle_dryer_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_range",
        "vol >= 50 && vol <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vol_bounded",
        "vol >= 50 && vol <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume in [50, 10000] L");
}

/// Test 2: Heat transfer area x10 m^2 (0.1 m^2 resolution) bounded [10, 5000].
#[test]
fn test_paddle_dryer_heat_area_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "area_x10 >= 10 && area_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_bounded",
        "area_x10 >= 10 && area_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heat transfer area x10 in [10, 5000]");
}

/// Test 3: Shaft speed x10 RPM (0.1 RPM resolution) bounded [5, 200].
#[test]
fn test_paddle_dryer_shaft_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spd_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spd_range",
        "spd_x10 >= 5 && spd_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spd_bounded",
        "spd_x10 >= 5 && spd_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shaft speed x10 in [5, 200]");
}

/// Test 4: Jacket temperature offset +500 (50 C to 300 C maps to 550..800).
#[test]
fn test_paddle_dryer_jacket_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 550 && temp <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 550 && temp <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jacket temp offset+500 in [550, 800]");
}

/// Test 5: Vacuum level x10 mbar (0.1 mbar resolution) bounded [1, 10000].
#[test]
fn test_paddle_dryer_vacuum_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vac_range",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vac_bounded",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level x10 in [1, 10000]");
}

/// Test 6: Target moisture x10 % (0.1% resolution) bounded [1, 500].
#[test]
fn test_paddle_dryer_moisture_target_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moist_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "moist_range",
        "moist_x10 >= 1 && moist_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "moist_bounded",
        "moist_x10 >= 1 && moist_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "moisture target x10 in [1, 500]");
}

/// Test 7: Heating medium 3-way (1=steam, 2=thermal oil, 3=hot water).
#[test]
fn test_paddle_dryer_heating_medium_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("med", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "med_range",
        "med == 1 || med == 2 || med == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "med_valid",
        "med == 1 || med == 2 || med == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heating medium is valid 3-way disjunction");
}

/// Test 8: Shaft configuration 3-way (1=single, 2=dual, 3=quad).
#[test]
fn test_paddle_dryer_shaft_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cfg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cfg_range",
        "cfg == 1 || cfg == 2 || cfg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cfg_valid",
        "cfg == 1 || cfg == 2 || cfg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shaft config is valid 3-way disjunction");
}

/// Test 9: Discharge method 3-way (1=gravity, 2=screw, 3=pneumatic).
#[test]
fn test_paddle_dryer_discharge_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dis_range",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dis_valid",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge method is valid 3-way disjunction");
}

/// Test 10: Dust collection boolean flag (0 or 1).
#[test]
fn test_paddle_dryer_dust_collection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dust", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dust_range",
        "dust == 0 || dust == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dust_valid",
        "dust == 0 || dust == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dust collection flag is boolean (0 or 1)");
}
