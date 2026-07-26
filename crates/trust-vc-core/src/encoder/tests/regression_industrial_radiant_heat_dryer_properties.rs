// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial radiant heat dryer property verification.
// Encodes key parameters of an industrial radiant heat dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Emitter temperature offset +100 (deg C) — bounded [200, 800].
/// 200 represents 100 C, 500 represents 400 C, 800 represents 700 C. Value 500.
#[test]
fn test_radiant_heat_dryer_emitter_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emitter_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "emitter_temp == 500"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "emitter_temp >= 200"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "emitter_temp <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "emitter temp 400 C (offset 500) in [200, 800]");
}

/// Test 2: Belt speed (x100 m/min) — bounded [1, 1000].
/// 250 represents 2.50 m/min. Value 250.
#[test]
fn test_radiant_heat_dryer_belt_speed_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("belt_speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "belt_speed == 250"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "belt_speed >= 1"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "belt_speed <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "belt speed 2.50 m/min (250 x100) in [1, 1000]");
}

/// Test 3: Radiant intensity (x10 kW/m2) — bounded [10, 500].
/// 150 represents 15.0 kW/m2. Value 150.
#[test]
fn test_radiant_heat_dryer_radiant_intensity_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("intensity", i32_ty());
    ctx.push_obligation(ProofObligation::assume("int_val", "intensity == 150"));
    ctx.push_obligation(ProofObligation::assert("int_min", "intensity >= 10"));
    ctx.push_obligation(ProofObligation::assert("int_max", "intensity <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "radiant intensity 15.0 kW/m2 (150 x10) in [10, 500]",
    );
}

/// Test 4: Product temperature offset +100 (deg C) — bounded [120, 350].
/// 120 represents 20 C, 220 represents 120 C, 350 represents 250 C. Value 220.
#[test]
fn test_radiant_heat_dryer_product_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("product_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ptemp_val", "product_temp == 220"));
    ctx.push_obligation(ProofObligation::assert("ptemp_min", "product_temp >= 120"));
    ctx.push_obligation(ProofObligation::assert("ptemp_max", "product_temp <= 350"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "product temp 120 C (offset 220) in [120, 350]");
}

/// Test 5: Emitter spacing (mm) — bounded [50, 500], value 150.
#[test]
fn test_radiant_heat_dryer_emitter_spacing_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spacing", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sp_val", "spacing == 150"));
    ctx.push_obligation(ProofObligation::assert("sp_min", "spacing >= 50"));
    ctx.push_obligation(ProofObligation::assert("sp_max", "spacing <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "emitter spacing 150 mm in [50, 500]");
}

/// Test 6: Dwell time (seconds) — bounded [5, 600], value 120.
#[test]
fn test_radiant_heat_dryer_dwell_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dwell_time", i32_ty());
    ctx.push_obligation(ProofObligation::assume("dwell_val", "dwell_time == 120"));
    ctx.push_obligation(ProofObligation::assert("dwell_min", "dwell_time >= 5"));
    ctx.push_obligation(ProofObligation::assert("dwell_max", "dwell_time <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dwell time 120 s in [5, 600]");
}

/// Test 7: Emitter type — 3-way disjunction.
/// 1=electric, 2=gas-catalytic, 3=ceramic. Value 2 (gas-catalytic).
#[test]
fn test_radiant_heat_dryer_emitter_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("emitter", i32_ty());
    ctx.push_obligation(ProofObligation::assume("etype_val", "emitter == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_emitter",
        "emitter == 1 || emitter == 2 || emitter == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "emitter type 2 (gas-catalytic) is valid 3-way disjunction",
    );
}

/// Test 8: Wavelength band — 3-way disjunction.
/// 1=short, 2=medium, 3=long. Value 1 (short).
#[test]
fn test_radiant_heat_dryer_wavelength_band_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("band", i32_ty());
    ctx.push_obligation(ProofObligation::assume("band_val", "band == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_band",
        "band == 1 || band == 2 || band == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wavelength band 1 (short) is valid 3-way disjunction",
    );
}

/// Test 9: Zone configuration — 3-way disjunction.
/// 1=single, 2=dual, 3=multi. Value 3 (multi).
#[test]
fn test_radiant_heat_dryer_zone_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zone_cfg", i32_ty());
    ctx.push_obligation(ProofObligation::assume("zcfg_val", "zone_cfg == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_zone_cfg",
        "zone_cfg == 1 || zone_cfg == 2 || zone_cfg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zone config 3 (multi) is valid 3-way disjunction");
}

/// Test 10: Automatic power modulation — boolean flag.
/// flag == 0 (disabled) or flag == 1 (enabled). Value 1.
#[test]
fn test_radiant_heat_dryer_auto_power_modulation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_val", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_flag",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto power modulation flag 1 is valid boolean");
}
