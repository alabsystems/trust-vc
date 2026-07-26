// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial spray dryer property verification.
// Encodes key parameters of an industrial spray dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Chamber diameter (mm) — bounded [1000, 8000], value 4000.
#[test]
fn test_spray_dryer_chamber_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "diameter == 4000"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "diameter >= 1000"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "diameter <= 8000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber diameter 4000 mm in [1000, 8000]");
}

/// Test 2: Inlet air temperature offset +500 (deg C) — bounded [650, 850].
/// 650 represents 150 C, 850 represents 350 C. Value 720 (220 C).
#[test]
fn test_spray_dryer_inlet_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_val",
        "inlet_temp_offset == 720",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_min",
        "inlet_temp_offset >= 650",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_max",
        "inlet_temp_offset <= 850",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet air temp 220 C (offset 720) in [650, 850]");
}

/// Test 3: Outlet air temperature offset +500 (deg C) — bounded [570, 620].
/// 570 represents 70 C, 620 represents 120 C. Value 590 (90 C).
#[test]
fn test_spray_dryer_outlet_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("outlet_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "outlet_val",
        "outlet_temp_offset == 590",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_min",
        "outlet_temp_offset >= 570",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_max",
        "outlet_temp_offset <= 620",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "outlet air temp 90 C (offset 590) in [570, 620]");
}

/// Test 4: Feed rate (x10 L/h) — scaled at 0.1 L/h, bounded [10, 5000].
/// 10 represents 1.0 L/h, 5000 represents 500.0 L/h. Value 1250 (125.0 L/h).
#[test]
fn test_spray_dryer_feed_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_x10 == 1250"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("feed_max", "feed_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 125.0 L/h (1250 x10) in [10, 5000]");
}

/// Test 5: Atomizer type — 3-way disjunction.
/// 1=rotary, 2=pressure nozzle, 3=two-fluid nozzle. Value 1 (rotary).
#[test]
fn test_spray_dryer_atomizer_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atomizer_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("atom_val", "atomizer_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_atomizer",
        "atomizer_type == 1 || atomizer_type == 2 || atomizer_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "atomizer type 1 (rotary) is valid 3-way disjunction",
    );
}

/// Test 6: Evaporation capacity (kg/h) — bounded [5, 1000], value 250.
#[test]
fn test_spray_dryer_evaporation_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_capacity", u32_ty());
    ctx.push_obligation(ProofObligation::assume("evap_val", "evap_capacity == 250"));
    ctx.push_obligation(ProofObligation::assert("evap_min", "evap_capacity >= 5"));
    ctx.push_obligation(ProofObligation::assert("evap_max", "evap_capacity <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evaporation capacity 250 kg/h in [5, 1000]");
}

/// Test 7: Cyclone type — 3-way disjunction.
/// 1=single, 2=multi-clone, 3=bag filter. Value 2 (multi-clone).
#[test]
fn test_spray_dryer_cyclone_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cyclone_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cyc_val", "cyclone_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_cyclone",
        "cyclone_type == 1 || cyclone_type == 2 || cyclone_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cyclone type 2 (multi-clone) is valid 3-way disjunction",
    );
}

/// Test 8: Residual moisture (x100 %) — scaled at 0.01%, bounded [50, 800].
/// 50 represents 0.50%, 800 represents 8.00%. Value 350 (3.50%).
#[test]
fn test_spray_dryer_residual_moisture_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moisture_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("moist_val", "moisture_x100 == 350"));
    ctx.push_obligation(ProofObligation::assert("moist_min", "moisture_x100 >= 50"));
    ctx.push_obligation(ProofObligation::assert("moist_max", "moisture_x100 <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residual moisture 3.50% (350 x100) in [50, 800]");
}

/// Test 9: Particle size (um) — bounded [10, 500], value 80.
#[test]
fn test_spray_dryer_particle_size_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("particle_um", u32_ty());
    ctx.push_obligation(ProofObligation::assume("part_val", "particle_um == 80"));
    ctx.push_obligation(ProofObligation::assert("part_min", "particle_um >= 10"));
    ctx.push_obligation(ProofObligation::assert("part_max", "particle_um <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "particle size 80 um in [10, 500]");
}

/// Test 10: CIP system — boolean flag using i32 with if/else pattern.
/// Flag 1 = clean-in-place system installed, cip_active = 1.
#[test]
fn test_spray_dryer_cip_system_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cip_flag", i32_ty());
    ctx.declare_var_typed("cip_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "cip_flag == 0 || cip_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "cip_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cip_def",
        "cip_active == if cip_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cip_enabled", "cip_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CIP flag activates clean-in-place system");
}
