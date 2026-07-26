// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial infrared dryer property verification.
// Encodes key parameters of an industrial infrared dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Emitter power (kW) — bounded [1, 200], value 50.
#[test]
fn test_infrared_dryer_emitter_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emitter_power_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_val",
        "emitter_power_kw == 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_min",
        "emitter_power_kw >= 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_max",
        "emitter_power_kw <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "emitter power 50 kW in [1, 200]");
}

/// Test 2: Wavelength (x10 um) — bounded [5, 200], value 30 (3.0 um).
#[test]
fn test_infrared_dryer_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wavelength_x10um", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wl_val", "wavelength_x10um == 30"));
    ctx.push_obligation(ProofObligation::assert("wl_min", "wavelength_x10um >= 5"));
    ctx.push_obligation(ProofObligation::assert("wl_max", "wavelength_x10um <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wavelength 3.0 um (30 x10) in [5, 200]");
}

/// Test 3: Belt speed (x10 m/min) — bounded [1, 200], value 50 (5.0 m/min).
#[test]
fn test_infrared_dryer_belt_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "belt_speed_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "belt_speed_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_max",
        "belt_speed_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt speed 5.0 m/min (50 x10) in [1, 200]");
}

/// Test 4: Emitter temperature offset +500 (deg C) — bounded [500, 2500], value 1500.
/// 500 represents 0 C, 1500 represents 1000 C, 2500 represents 2000 C.
#[test]
fn test_infrared_dryer_emitter_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emitter_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "emitter_temp_offset == 1500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "emitter_temp_offset >= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "emitter_temp_offset <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "emitter temp 1000 C (offset 1500) in [500, 2500]");
}

/// Test 5: Drying zone length (x10 m) — bounded [5, 200], value 100 (10.0 m).
#[test]
fn test_infrared_dryer_zone_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zone_length_x10m", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "len_val",
        "zone_length_x10m == 100",
    ));
    ctx.push_obligation(ProofObligation::assert("len_min", "zone_length_x10m >= 5"));
    ctx.push_obligation(ProofObligation::assert(
        "len_max",
        "zone_length_x10m <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying zone length 10.0 m (100 x10) in [5, 200]");
}

/// Test 6: Number of zones — bounded [1, 20], value 6.
#[test]
fn test_infrared_dryer_number_of_zones_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_zones", u32_ty());
    ctx.push_obligation(ProofObligation::assume("zones_val", "num_zones == 6"));
    ctx.push_obligation(ProofObligation::assert("zones_min", "num_zones >= 1"));
    ctx.push_obligation(ProofObligation::assert("zones_max", "num_zones <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of zones 6 in [1, 20]");
}

/// Test 7: Emitter type — 3-way disjunction.
/// 1=short-wave, 2=medium-wave, 3=long-wave. Value 2 (medium-wave).
#[test]
fn test_infrared_dryer_emitter_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emitter_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("etype_val", "emitter_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_emitter_type",
        "emitter_type == 1 || emitter_type == 2 || emitter_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "emitter type 2 (medium-wave) is valid 3-way disjunction",
    );
}

/// Test 8: Reflector geometry — 3-way disjunction.
/// 1=parabolic, 2=flat, 3=elliptical. Value 1 (parabolic).
#[test]
fn test_infrared_dryer_reflector_geometry_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reflector_geom", u32_ty());
    ctx.push_obligation(ProofObligation::assume("geom_val", "reflector_geom == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_reflector",
        "reflector_geom == 1 || reflector_geom == 2 || reflector_geom == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "reflector geometry 1 (parabolic) is valid 3-way disjunction",
    );
}

/// Test 9: Cooling method — 3-way disjunction.
/// 1=air-cooled, 2=water-cooled, 3=hybrid. Value 3 (hybrid).
#[test]
fn test_infrared_dryer_cooling_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cool_val", "cooling_method == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_cooling",
        "cooling_method == 1 || cooling_method == 2 || cooling_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling method 3 (hybrid) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic power modulation — boolean flag using i32 with if/else pattern.
/// Flag 1 = power modulation enabled, modulation_active should be 1.
#[test]
fn test_infrared_dryer_auto_power_modulation_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("modulation_flag", i32_ty());
    ctx.declare_var_typed("modulation_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "modulation_flag == 0 || modulation_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "modulation_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "modulation_def",
        "modulation_active == if modulation_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "modulation_enabled",
        "modulation_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "power modulation flag triggers modulation active");
}
