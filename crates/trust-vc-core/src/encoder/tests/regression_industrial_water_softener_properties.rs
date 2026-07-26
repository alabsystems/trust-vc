// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial water softener property verification.
// Encodes key parameters of an industrial water softening system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Flow rate (m³/h) — treated water flow bounded [1, 500], value 75.
#[test]
fn test_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_m3h", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_m3h == 75"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "flow_m3h >= 1"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "flow_m3h <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 75 m3/h in [1, 500]");
}

/// Test 2: Hardness removal (ppm) — inlet hardness bounded [50, 2000], value 350.
#[test]
fn test_hardness_removal_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hardness_ppm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hard_val", "hardness_ppm == 350"));
    ctx.push_obligation(ProofObligation::assert("hard_min", "hardness_ppm >= 50"));
    ctx.push_obligation(ProofObligation::assert("hard_max", "hardness_ppm <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hardness removal 350 ppm in [50, 2000]");
}

/// Test 3: Resin volume (L) — ion exchange resin bed volume bounded [10, 10000], value 800.
#[test]
fn test_resin_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resin_liters", u32_ty());
    ctx.push_obligation(ProofObligation::assume("resin_val", "resin_liters == 800"));
    ctx.push_obligation(ProofObligation::assert("resin_min", "resin_liters >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "resin_max",
        "resin_liters <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resin volume 800 L in [10, 10000]");
}

/// Test 4: Regeneration type — 3-way disjunction.
/// 1=time-based, 2=volume-based, 3=hardness-sensor. Value 2 (volume-based).
#[test]
fn test_regeneration_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("regen_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("regen_val", "regen_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_regen",
        "regen_type == 1 || regen_type == 2 || regen_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "regeneration type 2 (volume-based) is valid 3-way disjunction",
    );
}

/// Test 5: Salt dose (kg) — regeneration salt consumption bounded [1, 500], value 25.
#[test]
fn test_salt_dose_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("salt_kg", u32_ty());
    ctx.push_obligation(ProofObligation::assume("salt_val", "salt_kg == 25"));
    ctx.push_obligation(ProofObligation::assert("salt_min", "salt_kg >= 1"));
    ctx.push_obligation(ProofObligation::assert("salt_max", "salt_kg <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "salt dose 25 kg in [1, 500]");
}

/// Test 6: Vessel count — 3-way disjunction.
/// 1=simplex, 2=duplex, 3=triplex. Value 2 (duplex).
#[test]
fn test_vessel_count_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vessel_val", "vessel_count == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_vessel",
        "vessel_count == 1 || vessel_count == 2 || vessel_count == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vessel count 2 (duplex) is valid 3-way disjunction",
    );
}

/// Test 7: Backwash flow (L/min) — backwash rinse flow bounded [10, 5000], value 600.
#[test]
fn test_backwash_flow_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("backwash_lpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bw_val", "backwash_lpm == 600"));
    ctx.push_obligation(ProofObligation::assert("bw_min", "backwash_lpm >= 10"));
    ctx.push_obligation(ProofObligation::assert("bw_max", "backwash_lpm <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "backwash flow 600 L/min in [10, 5000]");
}

/// Test 8: Service cycle (hours) — time between regenerations bounded [1, 720], value 48.
#[test]
fn test_service_cycle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_hours", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cycle_val", "cycle_hours == 48"));
    ctx.push_obligation(ProofObligation::assert("cycle_min", "cycle_hours >= 1"));
    ctx.push_obligation(ProofObligation::assert("cycle_max", "cycle_hours <= 720"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "service cycle 48 hours in [1, 720]");
}

/// Test 9: Operating temperature offset +500 (deg C) — bounded [450, 600].
/// 450 represents -50 C, 600 represents 100 C. Value 525 (25 C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("op_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "op_temp_offset == 525"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "op_temp_offset >= 450"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "op_temp_offset <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 25 C (offset 525) in [450, 600]");
}

/// Test 10: Brine tank alarm — boolean flag using i32 with if/else pattern.
/// Flag 1 = brine tank level low, which triggers alarm (alarm_active = 1).
#[test]
fn test_brine_tank_alarm_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("brine_low_flag", i32_ty());
    ctx.declare_var_typed("alarm_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "brine_low_flag == 0 || brine_low_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "brine_low_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_def",
        "alarm_active == if brine_low_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "alarm_triggered",
        "alarm_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "brine tank low flag triggers alarm");
}
