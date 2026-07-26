// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial freeze granulator property verification.
// Encodes key parameters of a freeze granulation system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Granule size (×10 μm) — bounded [10, 50000].
/// 2500 represents 250.0 μm. Value 2500 (250.0 μm).
#[test]
fn test_granule_size_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("granule_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gran_val", "granule_x10 == 2500"));
    ctx.push_obligation(ProofObligation::assert("gran_min", "granule_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("gran_max", "granule_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "granule size 250.0 um (2500 x10) in [10, 50000]");
}

/// Test 2: Freezing temperature offset +500 (deg C) — bounded [304, 460].
/// 304 represents -196 C, 460 represents -40 C. Value 380 (-120 C).
#[test]
fn test_freezing_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freeze_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "freeze_temp_offset == 380",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "freeze_temp_offset >= 304",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "freeze_temp_offset <= 460",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "freezing temp -120 C (offset 380) in [304, 460]");
}

/// Test 3: Spray pressure (bar) — bounded [1, 20], value 5.
#[test]
fn test_spray_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_bar", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spray_val", "spray_bar == 5"));
    ctx.push_obligation(ProofObligation::assert("spray_min", "spray_bar >= 1"));
    ctx.push_obligation(ProofObligation::assert("spray_max", "spray_bar <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray pressure 5 bar in [1, 20]");
}

/// Test 4: Slurry feed rate (×100 mL/min) — bounded [10, 10000].
/// 2500 represents 25.00 mL/min. Value 2500 (25.00 mL/min).
#[test]
fn test_slurry_feed_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_x100 == 2500"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert("feed_max", "feed_x100 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "slurry feed rate 25.00 mL/min (2500 x100) in [10, 10000]",
    );
}

/// Test 5: Batch size (kg) — bounded [1, 200], value 50.
#[test]
fn test_batch_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_kg", u32_ty());
    ctx.push_obligation(ProofObligation::assume("batch_val", "batch_kg == 50"));
    ctx.push_obligation(ProofObligation::assert("batch_min", "batch_kg >= 1"));
    ctx.push_obligation(ProofObligation::assert("batch_max", "batch_kg <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch size 50 kg in [1, 200]");
}

/// Test 6: Nozzle count — bounded [1, 8], value 4.
#[test]
fn test_nozzle_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("nozzle_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("noz_val", "nozzle_count == 4"));
    ctx.push_obligation(ProofObligation::assert("noz_min", "nozzle_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("noz_max", "nozzle_count <= 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "nozzle count 4 in [1, 8]");
}

/// Test 7: Freezing medium — 3-way disjunction.
/// 1=liquid-nitrogen, 2=liquid-argon, 3=dry-ice-ethanol. Value 1 (liquid-nitrogen).
#[test]
fn test_freezing_medium_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freeze_medium", u32_ty());
    ctx.push_obligation(ProofObligation::assume("med_val", "freeze_medium == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_medium",
        "freeze_medium == 1 || freeze_medium == 2 || freeze_medium == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "freezing medium 1 (liquid-nitrogen) is valid 3-way disjunction",
    );
}

/// Test 8: Atomization type — 3-way disjunction.
/// 1=ultrasonic, 2=pressure, 3=rotary. Value 2 (pressure).
#[test]
fn test_atomization_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atom_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("atom_val", "atom_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_atomization",
        "atom_type == 1 || atom_type == 2 || atom_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atomization type 2 (pressure) is valid 3-way disjunction",
    );
}

/// Test 9: Granule morphology — 3-way disjunction.
/// 1=spherical, 2=irregular, 3=hollow. Value 1 (spherical).
#[test]
fn test_granule_morphology_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("morphology", u32_ty());
    ctx.push_obligation(ProofObligation::assume("morph_val", "morphology == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_morphology",
        "morphology == 1 || morphology == 2 || morphology == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "granule morphology 1 (spherical) is valid 3-way disjunction",
    );
}

/// Test 10: Continuous operation — boolean flag using i32 with if/else pattern.
/// Flag 1 = continuous mode enabled, which activates conveyor belt (conveyor_active = 1).
#[test]
fn test_continuous_operation_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("continuous_flag", i32_ty());
    ctx.declare_var_typed("conveyor_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "continuous_flag == 0 || continuous_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "continuous_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "conveyor_def",
        "conveyor_active == if continuous_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conveyor_triggered",
        "conveyor_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "continuous operation flag activates conveyor belt");
}
