// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial agitated filter dryer property verification.
// Encodes key parameters of an industrial agitated filter dryer and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Vessel volume (liters) — bounded [50, 25000].
#[test]
fn test_agitated_filter_dryer_vessel_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_range",
        "volume >= 50 && volume <= 25000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vol_check",
        "volume >= 50 && volume <= 25000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume bounded [50, 25000] liters");
}

/// Test 2: Jacket pressure x10 (0.1 bar resolution) — bounded [10, 60].
#[test]
fn test_agitated_filter_dryer_jacket_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_check",
        "press_x10 >= 10 && press_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jacket pressure x10 bounded [10, 60]");
}

/// Test 3: Agitator speed x10 (0.1 RPM resolution) — bounded [5, 200].
#[test]
fn test_agitated_filter_dryer_agitator_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm_x10 >= 5 && rpm_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_check",
        "rpm_x10 >= 5 && rpm_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "agitator speed x10 bounded [5, 200]");
}

/// Test 4: Filter area (m2) — bounded [1, 500].
#[test]
fn test_agitated_filter_dryer_filter_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "area >= 1 && area <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_check",
        "area >= 1 && area <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filter area bounded [1, 500] m2");
}

/// Test 5: Product temperature offset +100 (deg C) — bounded [80, 350].
/// 80 represents -20 C, 350 represents 250 C.
#[test]
fn test_agitated_filter_dryer_product_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 80 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_check",
        "temp_off >= 80 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product temp offset bounded [80, 350] represents -20 to 250 C",
    );
}

/// Test 6: Agitator type — 3-way disjunction (1=smoothing, 2=cutting, 3=combination).
#[test]
fn test_agitated_filter_dryer_agitator_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("at", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_domain",
        "at == 1 || at == 2 || at == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "at_check",
        "at == 1 || at == 2 || at == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "agitator type is valid 3-way disjunction");
}

/// Test 7: Filter medium — 3-way disjunction (1=sintered-metal, 2=woven-mesh, 3=multilayer).
#[test]
fn test_agitated_filter_dryer_filter_medium_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fm_domain",
        "fm == 1 || fm == 2 || fm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fm_check",
        "fm == 1 || fm == 2 || fm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filter medium is valid 3-way disjunction");
}

/// Test 8: Discharge type — 3-way disjunction (1=side-valve, 2=bottom-valve, 3=heel-discharge).
#[test]
fn test_agitated_filter_dryer_discharge_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_domain",
        "dt == 1 || dt == 2 || dt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_check",
        "dt == 1 || dt == 2 || dt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge type is valid 3-way disjunction");
}

/// Test 9: Auto heel filtration flag — boolean (0 or 1).
#[test]
fn test_agitated_filter_dryer_auto_heel_filtration_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_check",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto heel filtration flag is boolean (0 or 1)");
}

/// Test 10: Cake thickness (mm) — bounded [5, 500].
#[test]
fn test_agitated_filter_dryer_cake_thickness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thickness", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thick_range",
        "thickness >= 5 && thickness <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thick_check",
        "thickness >= 5 && thickness <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cake thickness bounded [5, 500] mm");
}
