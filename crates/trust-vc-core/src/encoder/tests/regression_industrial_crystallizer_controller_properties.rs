// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial crystallizer controller property verification.
// Encodes key parameters of an industrial crystallization process and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Vessel volume (L) — bounded [100, 100000], value 10000.
#[test]
fn test_vessel_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "volume == 10000"));
    ctx.push_obligation(ProofObligation::assert("vol_min", "volume >= 100"));
    ctx.push_obligation(ProofObligation::assert("vol_max", "volume <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vessel volume 10000 L in [100, 100000]");
}

/// Test 2: Supersaturation (x100) — bounded [100, 150], value 105 (1.05).
#[test]
fn test_supersaturation_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("super_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ss_val", "super_x100 == 105"));
    ctx.push_obligation(ProofObligation::assert("ss_min", "super_x100 >= 100"));
    ctx.push_obligation(ProofObligation::assert("ss_max", "super_x100 <= 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "supersaturation 1.05 (105 x100) in [100, 150]");
}

/// Test 3: Cooling rate (x10 deg C/h) — bounded [5, 200], value 50 (5.0 deg C/h).
#[test]
fn test_cooling_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cool_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cr_val", "cool_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("cr_min", "cool_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("cr_max", "cool_x10 <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling rate 5.0 deg C/h (50 x10) in [5, 200]");
}

/// Test 4: Crystallizer type — 3-way disjunction.
/// 1=cooling, 2=evaporative, 3=reactive. Value 1 (cooling).
#[test]
fn test_crystallizer_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cryst_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ct_val", "cryst_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_cryst",
        "cryst_type == 1 || cryst_type == 2 || cryst_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "crystallizer type 1 (cooling) is valid 3-way disjunction",
    );
}

/// Test 5: Agitator type — 3-way disjunction.
/// 1=anchor, 2=pitched blade, 3=Rushton. Value 2 (pitched blade).
#[test]
fn test_agitator_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("agit_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("at_val", "agit_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_agit",
        "agit_type == 1 || agit_type == 2 || agit_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "agitator type 2 (pitched blade) is valid 3-way disjunction",
    );
}

/// Test 6: Agitator speed (RPM) — bounded [5, 300], value 60.
#[test]
fn test_agitator_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sp_val", "speed == 60"));
    ctx.push_obligation(ProofObligation::assert("sp_min", "speed >= 5"));
    ctx.push_obligation(ProofObligation::assert("sp_max", "speed <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "agitator speed 60 RPM in [5, 300]");
}

/// Test 7: Seed addition (x10 g/L) — bounded [1, 200], value 50 (5.0 g/L).
#[test]
fn test_seed_addition_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sd_val", "seed_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("sd_min", "seed_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("sd_max", "seed_x10 <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seed addition 5.0 g/L (50 x10) in [1, 200]");
}

/// Test 8: Crystal size target (um) — bounded [50, 5000], value 500.
#[test]
fn test_crystal_size_target_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("size", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sz_val", "size == 500"));
    ctx.push_obligation(ProofObligation::assert("sz_min", "size >= 50"));
    ctx.push_obligation(ProofObligation::assert("sz_max", "size <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crystal size target 500 um in [50, 5000]");
}

/// Test 9: Process temperature (deg C) — bounded [10, 150], value 60.
/// All positive range, no offset needed.
#[test]
fn test_process_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tp_val", "temp == 60"));
    ctx.push_obligation(ProofObligation::assert("tp_min", "temp >= 10"));
    ctx.push_obligation(ProofObligation::assert("tp_max", "temp <= 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "process temp 60 deg C in [10, 150]");
}

/// Test 10: Fines dissolution — boolean flag using i32 with if/else pattern.
/// Flag 1 = fines dissolution enabled.
#[test]
fn test_fines_dissolution_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fines_flag", i32_ty());
    ctx.declare_var_typed("fines_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "fines_flag == 0 || fines_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "fines_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "active_def",
        "fines_active == if fines_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fines_enabled",
        "fines_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fines dissolution flag enables fines removal");
}
