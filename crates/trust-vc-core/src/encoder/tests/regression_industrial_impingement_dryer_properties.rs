// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial impingement dryer property verification.
// Encodes key parameters of an industrial impingement dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Jet velocity (x10 m/s) — scaled at 0.1 m/s, bounded [1, 1999].
/// 1 represents 0.1 m/s, 1999 represents 199.9 m/s. Value 500 (50.0 m/s).
#[test]
fn test_impingement_dryer_jet_velocity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vel_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vel_val", "vel_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("vel_pos", "vel_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("vel_max", "vel_x10 < 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jet velocity 50.0 m/s (500 x10) in (0, 2000)");
}

/// Test 2: Air temperature offset +100 (deg C) — bounded (100, 800).
/// 200 represents 100 C, 700 represents 600 C. Value 450 (350 C).
#[test]
fn test_impingement_dryer_air_temperature_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_off == 450"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_off > 100"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_off < 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air temperature 350 C (offset 450) in (100, 800)");
}

/// Test 3: Nozzle-to-surface distance (x10 mm) — scaled at 0.1 mm, bounded (0, 5000).
/// 10 represents 1.0 mm, 4999 represents 499.9 mm. Value 200 (20.0 mm).
#[test]
fn test_impingement_dryer_nozzle_distance_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dist_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dist_val", "dist_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert("dist_pos", "dist_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("dist_max", "dist_x10 < 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle distance 20.0 mm (200 x10) in (0, 5000)");
}

/// Test 4: Nozzle diameter (x100 mm) — scaled at 0.01 mm, bounded (0, 50000).
/// 100 represents 1.00 mm, 49999 represents 499.99 mm. Value 1200 (12.00 mm).
#[test]
fn test_impingement_dryer_nozzle_diameter_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("diam_val", "diam_x100 == 1200"));
    ctx.push_obligation(ProofObligation::assert("diam_pos", "diam_x100 > 0"));
    ctx.push_obligation(ProofObligation::assert("diam_max", "diam_x100 < 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nozzle diameter 12.00 mm (1200 x100) in (0, 50000)",
    );
}

/// Test 5: Web speed (x10 m/min) — scaled at 0.1 m/min, bounded (0, 50000).
/// 10 represents 1.0 m/min, 49999 represents 4999.9 m/min. Value 3000 (300.0 m/min).
#[test]
fn test_impingement_dryer_web_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed_x10 == 3000"));
    ctx.push_obligation(ProofObligation::assert("speed_pos", "speed_x10 > 0"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "speed_x10 < 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "web speed 300.0 m/min (3000 x10) in (0, 50000)");
}

/// Test 6: Number of nozzle rows — bounded [1, 50], value 12.
#[test]
fn test_impingement_dryer_nozzle_rows_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rows", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rows_val", "rows == 12"));
    ctx.push_obligation(ProofObligation::assert("rows_min", "rows >= 1"));
    ctx.push_obligation(ProofObligation::assert("rows_max", "rows <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle rows 12 in [1, 50]");
}

/// Test 7: Nozzle geometry — 3-way disjunction.
/// 1=round, 2=slot, 3=perforated-plate. Value 2 (slot).
#[test]
fn test_impingement_dryer_nozzle_geometry_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("geom", u32_ty());
    ctx.push_obligation(ProofObligation::assume("geom_val", "geom == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_geom",
        "geom == 1 || geom == 2 || geom == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "nozzle geometry 2 (slot) is valid 3-way disjunction",
    );
}

/// Test 8: Impingement pattern — 3-way disjunction.
/// 1=single-sided, 2=double-sided, 3=staggered. Value 1 (single-sided).
#[test]
fn test_impingement_dryer_pattern_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pattern", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pat_val", "pattern == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_pattern",
        "pattern == 1 || pattern == 2 || pattern == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impingement pattern 1 (single-sided) is valid 3-way disjunction",
    );
}

/// Test 9: Heating source — 3-way disjunction.
/// 1=gas-direct, 2=steam-indirect, 3=electric. Value 3 (electric).
#[test]
fn test_impingement_dryer_heating_source_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("source", u32_ty());
    ctx.push_obligation(ProofObligation::assume("src_val", "source == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_source",
        "source == 1 || source == 2 || source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating source 3 (electric) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic web tension control — boolean flag using i32 with if/else pattern.
/// Flag 1 = automatic web tension control enabled, tension_active = 1.
#[test]
fn test_impingement_dryer_auto_web_tension_control_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tension_flag", i32_ty());
    ctx.declare_var_typed("tension_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "tension_flag == 0 || tension_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "tension_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "tension_def",
        "tension_active == if tension_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tension_enabled",
        "tension_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto web tension control flag activates tension controller",
    );
}
