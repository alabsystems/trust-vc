// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial drum dryer property verification.
// Encodes key parameters of an industrial drum dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Drum diameter (mm) — bounded [500, 3000], value 1500.
#[test]
fn test_drum_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "diameter == 1500"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "diameter >= 500"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "diameter <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum diameter 1500 mm in [500, 3000]");
}

/// Test 2: Drum length (mm) — bounded [1000, 6000], value 3000.
#[test]
fn test_drum_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "length == 3000"));
    ctx.push_obligation(ProofObligation::assert("len_min", "length >= 1000"));
    ctx.push_obligation(ProofObligation::assert("len_max", "length <= 6000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum length 3000 mm in [1000, 6000]");
}

/// Test 3: Steam pressure (kPa) — bounded [100, 1000], value 500.
#[test]
fn test_steam_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pres_val", "pressure == 500"));
    ctx.push_obligation(ProofObligation::assert("pres_min", "pressure >= 100"));
    ctx.push_obligation(ProofObligation::assert("pres_max", "pressure <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "steam pressure 500 kPa in [100, 1000]");
}

/// Test 4: Drum type — 3-way disjunction.
/// 1=single, 2=double, 3=twin. Value 2 (double drum).
#[test]
fn test_drum_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drum_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dtype_val", "drum_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_drum_type",
        "drum_type == 1 || drum_type == 2 || drum_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum type 2 (double) is valid 3-way disjunction");
}

/// Test 5: Feed method — 3-way disjunction.
/// 1=dip, 2=nip, 3=splash. Value 1 (dip feed).
#[test]
fn test_feed_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fm_val", "feed_method == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_feed",
        "feed_method == 1 || feed_method == 2 || feed_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed method 1 (dip) is valid 3-way disjunction");
}

/// Test 6: Rotation speed (x100 RPM) — scaled speed bounded [10, 2000].
/// 500 represents 5.00 RPM. Value 500 (5.00 RPM rotation speed).
#[test]
fn test_rotation_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_x100 == 500"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_x100 <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 5.00 RPM (500 x100) in [10, 2000]");
}

/// Test 7: Film thickness (x100 mm) — scaled thickness bounded [5, 200].
/// 50 represents 0.50 mm. Value 50 (0.50 mm film thickness).
#[test]
fn test_film_thickness_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thick_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("thick_val", "thick_x100 == 50"));
    ctx.push_obligation(ProofObligation::assert("thick_min", "thick_x100 >= 5"));
    ctx.push_obligation(ProofObligation::assert("thick_max", "thick_x100 <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "film thickness 0.50 mm (50 x100) in [5, 200]");
}

/// Test 8: Evaporation rate (kg/h) — bounded [10, 2000], value 200.
#[test]
fn test_evaporation_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap", u32_ty());
    ctx.push_obligation(ProofObligation::assume("evap_val", "evap == 200"));
    ctx.push_obligation(ProofObligation::assert("evap_min", "evap >= 10"));
    ctx.push_obligation(ProofObligation::assert("evap_max", "evap <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evaporation rate 200 kg/h in [10, 2000]");
}

/// Test 9: Knife material — 3-way disjunction.
/// 1=carbon steel, 2=stainless, 3=chrome plated. Value 3 (chrome plated).
#[test]
fn test_knife_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("knife_mat", u32_ty());
    ctx.push_obligation(ProofObligation::assume("km_val", "knife_mat == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_knife",
        "knife_mat == 1 || knife_mat == 2 || knife_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "knife material 3 (chrome plated) is valid 3-way disjunction",
    );
}

/// Test 10: Condensate removal — boolean flag using i32 with if/else pattern.
/// Flag 1 = condensate removal system installed, removal_active = 1.
#[test]
fn test_condensate_removal_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond_flag", i32_ty());
    ctx.declare_var_typed("removal_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "cond_flag == 0 || cond_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "cond_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "removal_def",
        "removal_active == if cond_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("removal_on", "removal_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "condensate removal flag activates removal system");
}
