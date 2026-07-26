// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial freeze dryer controller property verification.
// Encodes key parameters of an industrial freeze dryer (lyophilizer) system
// and verifies that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Shelf area (×100 m²) — bounded [10, 10000].
/// 500 represents 5.00 m². Value 500 (5.00 m²).
#[test]
fn test_shelf_area_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelf_area_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_val",
        "shelf_area_x100 == 500",
    ));
    ctx.push_obligation(ProofObligation::assert("area_min", "shelf_area_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "area_max",
        "shelf_area_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf area 5.00 m2 (500 x100) in [10, 10000]");
}

/// Test 2: Condenser temperature offset +500 (deg C) — bounded [380, 480].
/// 380 represents -120 C, 480 represents -20 C. Value 430 (-70 C).
#[test]
fn test_condenser_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cond_val",
        "cond_temp_offset == 430",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cond_min",
        "cond_temp_offset >= 380",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cond_max",
        "cond_temp_offset <= 480",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "condenser temp -70 C (offset 430) in [380, 480]");
}

/// Test 3: Chamber vacuum (Pa) — bounded [1, 500], value 13.
/// 13 Pa is a typical primary drying vacuum for pharmaceutical lyophilization.
#[test]
fn test_chamber_vacuum_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chamber_pa", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "chamber_pa == 13"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "chamber_pa >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "chamber_pa <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "chamber vacuum 13 Pa in [1, 500]");
}

/// Test 4: Shelf temperature offset +500 (deg C) — bounded [400, 600].
/// 400 represents -100 C, 600 represents +100 C. Value 470 (-30 C).
#[test]
fn test_shelf_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shelf_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shelf_val",
        "shelf_temp_offset == 470",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shelf_min",
        "shelf_temp_offset >= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shelf_max",
        "shelf_temp_offset <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shelf temp -30 C (offset 470) in [400, 600]");
}

/// Test 5: Drying phase — 3-way disjunction.
/// 1=freezing, 2=primary drying, 3=secondary drying. Value 2 (primary drying).
#[test]
fn test_drying_phase_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drying_phase", u32_ty());
    ctx.push_obligation(ProofObligation::assume("phase_val", "drying_phase == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_phase",
        "drying_phase == 1 || drying_phase == 2 || drying_phase == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drying phase 2 (primary drying) is valid 3-way disjunction",
    );
}

/// Test 6: Refrigerant type — 3-way disjunction.
/// 1=R404A, 2=R507, 3=LN2. Value 3 (LN2 / liquid nitrogen).
#[test]
fn test_refrigerant_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrigerant_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("refr_val", "refrigerant_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_refrigerant",
        "refrigerant_type == 1 || refrigerant_type == 2 || refrigerant_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refrigerant type 3 (LN2) is valid 3-way disjunction",
    );
}

/// Test 7: Tray count — bounded [1, 50], value 12.
#[test]
fn test_tray_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tray_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tray_val", "tray_count == 12"));
    ctx.push_obligation(ProofObligation::assert("tray_min", "tray_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("tray_max", "tray_count <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tray count 12 in [1, 50]");
}

/// Test 8: Sublimation rate (×100 kg/h) — bounded [1, 5000].
/// 150 represents 1.50 kg/h. Value 150 (1.50 kg/h).
#[test]
fn test_sublimation_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sub_rate_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sub_val", "sub_rate_x100 == 150"));
    ctx.push_obligation(ProofObligation::assert("sub_min", "sub_rate_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("sub_max", "sub_rate_x100 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sublimation rate 1.50 kg/h (150 x100) in [1, 5000]",
    );
}

/// Test 9: Defrost interval (min) — bounded [30, 480], value 120.
#[test]
fn test_defrost_interval_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("defrost_min", u32_ty());
    ctx.push_obligation(ProofObligation::assume("defr_val", "defrost_min == 120"));
    ctx.push_obligation(ProofObligation::assert("defr_lo", "defrost_min >= 30"));
    ctx.push_obligation(ProofObligation::assert("defr_hi", "defrost_min <= 480"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "defrost interval 120 min in [30, 480]");
}

/// Test 10: Stoppering mechanism — boolean flag using i32 with if/else pattern.
/// Flag 1 = stoppering enabled, which activates hydraulic ram (ram_active = 1).
#[test]
fn test_stoppering_mechanism_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stopper_flag", i32_ty());
    ctx.declare_var_typed("ram_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "stopper_flag == 0 || stopper_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "stopper_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ram_def",
        "ram_active == if stopper_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ram_triggered", "ram_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "stoppering flag activates hydraulic ram");
}
