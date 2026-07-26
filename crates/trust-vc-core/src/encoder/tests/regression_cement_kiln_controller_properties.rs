// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Cement kiln controller property verification.
// Encodes key parameters of a rotary cement kiln system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Kiln diameter (mm) — bounded [2000, 8000], value 4500.
#[test]
fn test_kiln_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "diameter_mm == 4500"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "diameter_mm >= 2000"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "diameter_mm <= 8000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "kiln diameter 4500 mm in [2000, 8000]");
}

/// Test 2: Kiln length (m) — bounded [30, 120], value 75.
#[test]
fn test_kiln_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("length_m", u32_ty());
    ctx.push_obligation(ProofObligation::assume("len_val", "length_m == 75"));
    ctx.push_obligation(ProofObligation::assert("len_min", "length_m >= 30"));
    ctx.push_obligation(ProofObligation::assert("len_max", "length_m <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "kiln length 75 m in [30, 120]");
}

/// Test 3: Burning zone temperature (deg C) — bounded [1200, 1600], value 1450.
/// All values positive so no offset needed.
#[test]
fn test_burning_zone_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("burn_temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bt_val", "burn_temp_c == 1450"));
    ctx.push_obligation(ProofObligation::assert("bt_min", "burn_temp_c >= 1200"));
    ctx.push_obligation(ProofObligation::assert("bt_max", "burn_temp_c <= 1600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "burning zone temp 1450 C in [1200, 1600]");
}

/// Test 4: Kiln type — 3-way disjunction.
/// 1=wet, 2=dry, 3=semi-dry. Value 2 (dry).
#[test]
fn test_kiln_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("kiln_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("kt_val", "kiln_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_kiln_type",
        "kiln_type == 1 || kiln_type == 2 || kiln_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "kiln type 2 (dry) is valid 3-way disjunction");
}

/// Test 5: Fuel type — 4-way disjunction.
/// 1=coal, 2=natural gas, 3=pet coke, 4=alternative fuel. Value 3 (pet coke).
#[test]
fn test_fuel_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fuel_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ft_val", "fuel_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_fuel",
        "fuel_type == 1 || fuel_type == 2 || fuel_type == 3 || fuel_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fuel type 3 (pet coke) is valid 4-way disjunction");
}

/// Test 6: Rotation speed (x100 RPM) — 1.50 RPM = 150, bounded [50, 500], value 200 (2.0 RPM).
#[test]
fn test_rotation_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_x100 == 200"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_x100 >= 50"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_x100 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 2.0 RPM (200 x100) in [50, 500]");
}

/// Test 7: Feed rate (t/h) — bounded [50, 1000], value 350.
#[test]
fn test_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_tph", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fr_val", "feed_tph == 350"));
    ctx.push_obligation(ProofObligation::assert("fr_min", "feed_tph >= 50"));
    ctx.push_obligation(ProofObligation::assert("fr_max", "feed_tph <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 350 t/h in [50, 1000]");
}

/// Test 8: Clinker cooler type — 3-way disjunction.
/// 1=grate, 2=planetary, 3=rotary. Value 1 (grate).
#[test]
fn test_clinker_cooler_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooler_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ct_val", "cooler_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_cooler",
        "cooler_type == 1 || cooler_type == 2 || cooler_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooler type 1 (grate) is valid 3-way disjunction");
}

/// Test 9: Draft pressure (Pa) — bounded [100, 5000], value 2500.
#[test]
fn test_draft_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("draft_pa", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dp_val", "draft_pa == 2500"));
    ctx.push_obligation(ProofObligation::assert("dp_min", "draft_pa >= 100"));
    ctx.push_obligation(ProofObligation::assert("dp_max", "draft_pa <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "draft pressure 2500 Pa in [100, 5000]");
}

/// Test 10: NOx monitoring — boolean flag using i32 with if/else pattern.
/// Flag 1 = NOx above threshold, which triggers scrubber (scrubber_active = 1).
#[test]
fn test_nox_monitoring_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nox_high_flag", i32_ty());
    ctx.declare_var_typed("scrubber_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "nox_high_flag == 0 || nox_high_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "nox_high_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "scrubber_def",
        "scrubber_active == if nox_high_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "scrubber_triggered",
        "scrubber_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NOx high flag triggers scrubber");
}
