// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Reflow oven controller property verification.
// Encodes key parameters of a reflow soldering oven and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Peak temperature (deg C) — bounded [200, 300], value 245.
#[test]
fn test_peak_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("peak_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("peak_val", "peak_temp == 245"));
    ctx.push_obligation(ProofObligation::assert("peak_min", "peak_temp >= 200"));
    ctx.push_obligation(ProofObligation::assert("peak_max", "peak_temp <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "peak temperature 245 C in [200, 300]");
}

/// Test 2: Preheat temperature (deg C) — bounded [100, 220], value 180.
#[test]
fn test_preheat_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("preheat_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "preheat_val",
        "preheat_temp == 180",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "preheat_min",
        "preheat_temp >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "preheat_max",
        "preheat_temp <= 220",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "preheat temperature 180 C in [100, 220]");
}

/// Test 3: Zone count — bounded [4, 16], value 10.
#[test]
fn test_zone_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("zones", u32_ty());
    ctx.push_obligation(ProofObligation::assume("zones_val", "zones == 10"));
    ctx.push_obligation(ProofObligation::assert("zones_min", "zones >= 4"));
    ctx.push_obligation(ProofObligation::assert("zones_max", "zones <= 16"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "zone count 10 in [4, 16]");
}

/// Test 4: Conveyor speed (x10 cm/min) — bounded [100, 2000], value 800 (80.0 cm/min).
#[test]
fn test_conveyor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed_x10 == 800"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "speed_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "speed_x10 <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "conveyor speed 80.0 cm/min (800 x10) in [100, 2000]",
    );
}

/// Test 5: Heating type — 3-way disjunction.
/// 1=IR, 2=convection, 3=vapor phase. Value 1 (IR).
#[test]
fn test_heating_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("heating_val", "heating_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heating",
        "heating_type == 1 || heating_type == 2 || heating_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heating type 1 (IR) is valid 3-way disjunction");
}

/// Test 6: Solder type — 3-way disjunction.
/// 1=SnPb, 2=lead-free SAC, 3=low-temp BiSn. Value 2 (lead-free SAC).
#[test]
fn test_solder_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solder_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("solder_val", "solder_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_solder",
        "solder_type == 1 || solder_type == 2 || solder_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solder type 2 (lead-free SAC) is valid 3-way disjunction",
    );
}

/// Test 7: Board width max (mm) — bounded [50, 800], value 500.
#[test]
fn test_board_width_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width", u32_ty());
    ctx.push_obligation(ProofObligation::assume("width_val", "width == 500"));
    ctx.push_obligation(ProofObligation::assert("width_min", "width >= 50"));
    ctx.push_obligation(ProofObligation::assert("width_max", "width <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "board width 500 mm in [50, 800]");
}

/// Test 8: Cooling rate (x10 deg C/s) — bounded [5, 60], value 30 (3.0 deg C/s).
#[test]
fn test_cooling_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cool_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cool_val", "cool_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("cool_min", "cool_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("cool_max", "cool_x10 <= 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling rate 3.0 C/s (30 x10) in [5, 60]");
}

/// Test 9: Profile type — 3-way disjunction.
/// 1=ramp-soak-spike, 2=ramp-to-spike, 3=saddle. Value 1 (ramp-soak-spike).
#[test]
fn test_profile_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("profile_val", "profile_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_profile",
        "profile_type == 1 || profile_type == 2 || profile_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "profile type 1 (ramp-soak-spike) is valid 3-way disjunction",
    );
}

/// Test 10: Nitrogen atmosphere — boolean flag using i32 with if/else pattern.
/// Flag 1 = nitrogen enabled, n2_active = 1.
#[test]
fn test_nitrogen_atmosphere_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n2_flag", i32_ty());
    ctx.declare_var_typed("n2_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "n2_flag == 0 || n2_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "n2_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "n2_def",
        "n2_active == if n2_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "nitrogen_enabled",
        "n2_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nitrogen atmosphere flag enables N2 mode");
}
