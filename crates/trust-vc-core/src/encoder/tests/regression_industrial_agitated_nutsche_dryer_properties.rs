// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial agitated nutsche filter dryer property verification.
// Encodes key parameters of an agitated nutsche filter dryer (combined filtration
// and drying vessel used in pharmaceutical and chemical processing) and verifies
// bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Vessel diameter (mm) — bounded [500, 3000].
#[test]
fn test_nutsche_dryer_vessel_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diam_range",
        "diam >= 500 && diam <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diam_bounded",
        "diam >= 500 && diam <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel diameter must be between 500 and 3000 mm");
}

/// Test 2: Agitator speed (RPM) — bounded [5, 100].
#[test]
fn test_nutsche_dryer_agitator_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 5 && speed <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 5 && speed <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "agitator speed must be between 5 and 100 RPM");
}

/// Test 3: Filtration area x10 (representing 0.5-50.0 m^2) — bounded [5, 500].
#[test]
fn test_nutsche_dryer_filtration_area_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "area_x10 >= 5 && area_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_bounded",
        "area_x10 >= 5 && area_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "filtration area x10 must be between 5 and 500 (0.5-50.0 m2)",
    );
}

/// Test 4: Vessel pressure x10 (representing 0.1-6.0 bar) — bounded [1, 60].
#[test]
fn test_nutsche_dryer_vessel_pressure_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 1 && press_x10 <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 1 && press_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vessel pressure x10 must be between 1 and 60 (0.1-6.0 bar)",
    );
}

/// Test 5: Jacket temperature offset+100 (representing -40 to 250 deg C) — bounded [60, 350].
#[test]
fn test_nutsche_dryer_jacket_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 60 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 60 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature offset+100 must be between 60 and 350 (-40 to 250 C)",
    );
}

/// Test 6: Number of filter plates — bounded [1, 8].
#[test]
fn test_nutsche_dryer_filter_plates_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plates", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "plates_range",
        "plates >= 1 && plates <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "plates_bounded",
        "plates >= 1 && plates <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of filter plates must be between 1 and 8");
}

/// Test 7: Agitator blade type — 3-way disjunction.
/// 1=anchor, 2=paddle, 3=helical-ribbon.
#[test]
fn test_nutsche_dryer_blade_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blade_range",
        "blade == 1 || blade == 2 || blade == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blade_valid",
        "blade == 1 || blade == 2 || blade == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "agitator blade type must be anchor(1), paddle(2), or helical-ribbon(3)",
    );
}

/// Test 8: Drying mode — 3-way disjunction.
/// 1=vacuum, 2=pressure, 3=combined.
#[test]
fn test_nutsche_dryer_drying_mode_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_range",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drying mode must be vacuum(1), pressure(2), or combined(3)",
    );
}

/// Test 9: Filter medium — 3-way disjunction.
/// 1=sintered-metal, 2=cloth, 3=multilayer.
#[test]
fn test_nutsche_dryer_filter_medium_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("medium", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "medium_range",
        "medium == 1 || medium == 2 || medium == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "medium_valid",
        "medium == 1 || medium == 2 || medium == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "filter medium must be sintered-metal(1), cloth(2), or multilayer(3)",
    );
}

/// Test 10: Automatic CIP cleaning — boolean flag (0 or 1).
#[test]
fn test_nutsche_dryer_cip_cleaning_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cip", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cip_range", "cip == 0 || cip == 1"));
    ctx.push_obligation(ProofObligation::assert("cip_valid", "cip == 0 || cip == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic CIP cleaning flag must be 0 (off) or 1 (on)",
    );
}
