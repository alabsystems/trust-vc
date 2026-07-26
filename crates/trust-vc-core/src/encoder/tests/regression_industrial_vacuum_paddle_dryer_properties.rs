// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial vacuum paddle dryer property verification.
// A horizontal jacketed vessel with heated paddles for drying under vacuum,
// used for solvents and heat-sensitive chemicals. Encodes key parameters and
// verifies bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Paddle speed (RPM) — bounded [1, 40], value 15.
#[test]
fn test_paddle_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("paddle_speed_rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_val",
        "paddle_speed_rpm == 15",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_min",
        "paddle_speed_rpm >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_max",
        "paddle_speed_rpm <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paddle speed 15 RPM in [1, 40]");
}

/// Test 2: Vessel volume (L) — bounded [50, 20000], value 2500.
#[test]
fn test_vessel_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_volume_l", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_val",
        "vessel_volume_l == 2500",
    ));
    ctx.push_obligation(ProofObligation::assert("vol_min", "vessel_volume_l >= 50"));
    ctx.push_obligation(ProofObligation::assert(
        "vol_max",
        "vessel_volume_l <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume 2500 L in [50, 20000]");
}

/// Test 3: Jacket temperature offset+100 (deg C) — bounded [60, 400].
/// Represents actual range -40 to 300 deg C. Value 220 (actual 120 deg C).
#[test]
fn test_jacket_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_off100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "jacket_temp_off100 == 220",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "jacket_temp_off100 >= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "jacket_temp_off100 <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature offset+100 220 (120 C) in [60, 400]",
    );
}

/// Test 4: Vacuum level x10 (mbar) — bounded [1, 10000].
/// Represents actual range 0.1-1000.0 mbar. Value 50 (actual 5.0 mbar).
#[test]
fn test_vacuum_level_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vacuum_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vacuum_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vacuum_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 5.0 mbar (50 x10) in [1, 10000]");
}

/// Test 5: Heat transfer area x10 (m^2) — bounded [10, 2000].
/// Represents actual range 1.0-200.0 m^2. Value 150 (actual 15.0 m^2).
#[test]
fn test_heat_transfer_area_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ht_area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume("area_val", "ht_area_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert("area_min", "ht_area_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("area_max", "ht_area_x10 <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heat transfer area 15.0 m^2 (150 x10) in [10, 2000]",
    );
}

/// Test 6: Number of paddle shafts — bounded [1, 4], value 2.
#[test]
fn test_number_of_paddle_shafts_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shaft_count", i32_ty());
    ctx.push_obligation(ProofObligation::assume("shaft_val", "shaft_count == 2"));
    ctx.push_obligation(ProofObligation::assert("shaft_min", "shaft_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("shaft_max", "shaft_count <= 4"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paddle shaft count 2 in [1, 4]");
}

/// Test 7: Paddle design — 3-way disjunction.
/// 1=wedge, 2=disc, 3=sigma. Value 1 (wedge).
#[test]
fn test_paddle_design_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("paddle_design", i32_ty());
    ctx.push_obligation(ProofObligation::assume("design_val", "paddle_design == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_design",
        "paddle_design == 1 || paddle_design == 2 || paddle_design == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "paddle design 1 (wedge) is valid 3-way disjunction",
    );
}

/// Test 8: Heating medium — 3-way disjunction.
/// 1=steam, 2=thermal-oil, 3=hot-water. Value 2 (thermal-oil).
#[test]
fn test_heating_medium_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating_medium", i32_ty());
    ctx.push_obligation(ProofObligation::assume("medium_val", "heating_medium == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_medium",
        "heating_medium == 1 || heating_medium == 2 || heating_medium == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating medium 2 (thermal-oil) is valid 3-way disjunction",
    );
}

/// Test 9: Vapor collection — 3-way disjunction.
/// 1=shell-condenser, 2=spray-condenser, 3=bag-filter. Value 3 (bag-filter).
#[test]
fn test_vapor_collection_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vapor_collection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vapor_val",
        "vapor_collection == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_vapor",
        "vapor_collection == 1 || vapor_collection == 2 || vapor_collection == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vapor collection 3 (bag-filter) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic solvent recovery — boolean flag (0 or 1), value 1 (enabled).
#[test]
fn test_automatic_solvent_recovery_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solvent_recovery_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sr_val",
        "solvent_recovery_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sr_boolean",
        "solvent_recovery_flag == 0 || solvent_recovery_flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solvent recovery flag 1 is valid boolean (0 or 1)");
}
