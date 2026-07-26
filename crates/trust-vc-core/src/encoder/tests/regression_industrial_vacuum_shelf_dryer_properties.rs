// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial vacuum shelf dryer property verification tests.
// Encodes key parameters of a vacuum shelf dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.
// All variables use i32_ty() with integer scaling to avoid floating-point.

/// Test 1: Shelf count — bounded [2, 50].
#[test]
fn test_vacuum_shelf_dryer_shelf_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelves", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shelves_bounds",
        "shelves >= 2 && shelves <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shelves_valid",
        "shelves >= 2 && shelves <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf count within 2-50 range");
}

/// Test 2: Shelf area (m2) — bounded [1, 200].
#[test]
fn test_vacuum_shelf_dryer_shelf_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_bounds",
        "area >= 1 && area <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_valid",
        "area >= 1 && area <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf area within 1-200 m2 range");
}

/// Test 3: Vacuum level (scaled x10, units: 0.1 mbar) — bounded [1, 10000].
/// vac_x10 = 50 represents 5.0 mbar.
#[test]
fn test_vacuum_shelf_dryer_vacuum_level_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vac_bounds",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vac_valid",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level within 0.1-1000.0 mbar scaled range");
}

/// Test 4: Shelf temperature (offset +100, units: deg C) — bounded [80, 350].
/// Actual temperature = temp_off - 100, covering -20 C to 250 C.
#[test]
fn test_vacuum_shelf_dryer_shelf_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_bounds",
        "temp_off >= 80 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_valid",
        "temp_off >= 80 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shelf temperature offset within -20 to 250 C range",
    );
}

/// Test 5: Drying time (hours) — bounded [1, 2000].
#[test]
fn test_vacuum_shelf_dryer_drying_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_bounds",
        "time >= 1 && time <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_valid",
        "time >= 1 && time <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying time within 1-2000 hours range");
}

/// Test 6: Heating method — 3-way disjunction.
/// 1=steam, 2=hot-water, 3=electric.
#[test]
fn test_vacuum_shelf_dryer_heating_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hm_valid",
        "hm == 1 || hm == 2 || hm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("hm_in_range", "hm >= 1 && hm <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method is one of steam, hot-water, or electric",
    );
}

/// Test 7: Shelf material — 3-way disjunction.
/// 1=stainless-steel, 2=carbon-steel, 3=hastelloy.
#[test]
fn test_vacuum_shelf_dryer_shelf_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_valid",
        "sm == 1 || sm == 2 || sm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("sm_in_range", "sm >= 1 && sm <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "shelf material is one of stainless-steel, carbon-steel, or hastelloy",
    );
}

/// Test 8: Door type — 3-way disjunction.
/// 1=front-opening, 2=top-opening, 3=side-opening.
#[test]
fn test_vacuum_shelf_dryer_door_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_valid",
        "dt == 1 || dt == 2 || dt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("dt_in_range", "dt >= 1 && dt <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "door type is one of front-opening, top-opening, or side-opening",
    );
}

/// Test 9: Automatic temperature ramp flag — boolean encoded as i32.
/// 0=disabled, 1=enabled.
#[test]
fn test_vacuum_shelf_dryer_auto_temperature_ramp_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_boolean",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_bounded",
        "flag >= 0 && flag <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto temperature ramp flag is a valid boolean encoding",
    );
}

/// Test 10: Condenser capacity (kg/batch) — bounded [10, 5000].
#[test]
fn test_vacuum_shelf_dryer_condenser_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "capacity_bounds",
        "capacity >= 10 && capacity <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "capacity_valid",
        "capacity >= 10 && capacity <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "condenser capacity within 10-5000 kg/batch range");
}
