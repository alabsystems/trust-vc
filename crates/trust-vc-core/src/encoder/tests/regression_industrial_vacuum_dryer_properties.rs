// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial vacuum dryer property verification.
// Encodes key parameters of an industrial vacuum dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Chamber volume (L) — bounded [10, 5000], value 800.
#[test]
fn test_chamber_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber_volume_l", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vol_val",
        "chamber_volume_l == 800",
    ));
    ctx.push_obligation(ProofObligation::assert("vol_min", "chamber_volume_l >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "vol_max",
        "chamber_volume_l <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber volume 800 L in [10, 5000]");
}

/// Test 2: Vacuum level (×10 mbar) — bounded [1, 10000].
/// 50 represents 5.0 mbar. Value 50 (5.0 mbar).
#[test]
fn test_vacuum_level_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vacuum_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vacuum_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vacuum_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level 5.0 mbar (50 x10) in [1, 10000]");
}

/// Test 3: Shelf temperature (deg C) — bounded [20, 200], value 80.
#[test]
fn test_shelf_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelf_temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "shelf_temp_c == 80"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "shelf_temp_c >= 20"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "shelf_temp_c <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf temperature 80 C in [20, 200]");
}

/// Test 4: Drying time (hours) — bounded [1, 72], value 24.
#[test]
fn test_drying_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drying_hours", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dry_val", "drying_hours == 24"));
    ctx.push_obligation(ProofObligation::assert("dry_min", "drying_hours >= 1"));
    ctx.push_obligation(ProofObligation::assert("dry_max", "drying_hours <= 72"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying time 24 hours in [1, 72]");
}

/// Test 5: Condenser capacity (×10 kg/h) — bounded [1, 1000].
/// 250 represents 25.0 kg/h. Value 250 (25.0 kg/h).
#[test]
fn test_condenser_capacity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond_cap_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cond_val", "cond_cap_x10 == 250"));
    ctx.push_obligation(ProofObligation::assert("cond_min", "cond_cap_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("cond_max", "cond_cap_x10 <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condenser capacity 25.0 kg/h (250 x10) in [1, 1000]",
    );
}

/// Test 6: Dryer type — 3-way disjunction.
/// 1=shelf, 2=tumble, 3=conical. Value 1 (shelf).
#[test]
fn test_dryer_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dryer_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dryer_val", "dryer_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_dryer",
        "dryer_type == 1 || dryer_type == 2 || dryer_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dryer type 1 (shelf) is valid 3-way disjunction");
}

/// Test 7: Heating method — 3-way disjunction.
/// 1=steam, 2=hot-water, 3=electric. Value 2 (hot-water).
#[test]
fn test_heating_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("heat_val", "heating_method == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heating",
        "heating_method == 1 || heating_method == 2 || heating_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method 2 (hot-water) is valid 3-way disjunction",
    );
}

/// Test 8: Condenser type — 3-way disjunction.
/// 1=internal, 2=external, 3=plate. Value 3 (plate).
#[test]
fn test_condenser_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("condenser_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cond_type_val",
        "condenser_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_condenser",
        "condenser_type == 1 || condenser_type == 2 || condenser_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condenser type 3 (plate) is valid 3-way disjunction",
    );
}

/// Test 9: Number of shelves — bounded [1, 20], value 8.
#[test]
fn test_number_of_shelves_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelf_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("shelf_val", "shelf_count == 8"));
    ctx.push_obligation(ProofObligation::assert("shelf_min", "shelf_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("shelf_max", "shelf_count <= 20"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf count 8 in [1, 20]");
}

/// Test 10: Inert gas blanketing — boolean flag using i32 with if/else pattern.
/// Flag 1 = inert gas enabled, which activates nitrogen supply (n2_active = 1).
#[test]
fn test_inert_gas_blanketing_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inert_gas_flag", i32_ty());
    ctx.declare_var_typed("n2_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "inert_gas_flag == 0 || inert_gas_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "inert_gas_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "n2_def",
        "n2_active == if inert_gas_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("n2_triggered", "n2_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "inert gas blanketing flag activates nitrogen supply",
    );
}
