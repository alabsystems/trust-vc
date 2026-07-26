// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial ribbon blender property verification.
// Encodes key parameters of an industrial ribbon blender system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Working capacity (L) — ribbon blender vessel capacity bounded [50, 20000], value 2000.
#[test]
fn test_working_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capacity_l", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "capacity_l == 2000"));
    ctx.push_obligation(ProofObligation::assert("cap_min", "capacity_l >= 50"));
    ctx.push_obligation(ProofObligation::assert("cap_max", "capacity_l <= 20000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "working capacity 2000 L in [50, 20000]");
}

/// Test 2: Motor power (kW) — drive motor rated power bounded [5, 500], value 75.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "motor_kw == 75"));
    ctx.push_obligation(ProofObligation::assert("pwr_min", "motor_kw >= 5"));
    ctx.push_obligation(ProofObligation::assert("pwr_max", "motor_kw <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 75 kW in [5, 500]");
}

/// Test 3: Ribbon speed (RPM) — agitator ribbon rotational speed bounded [5, 100], value 30.
#[test]
fn test_ribbon_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_rpm == 30"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_rpm >= 5"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_rpm <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ribbon speed 30 RPM in [5, 100]");
}

/// Test 4: Blender type — 3-way disjunction.
/// 1=single ribbon, 2=double ribbon, 3=paddle. Value 2 (double ribbon).
#[test]
fn test_blender_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blender_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("btype_val", "blender_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_blender",
        "blender_type == 1 || blender_type == 2 || blender_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blender type 2 (double ribbon) is valid 3-way disjunction",
    );
}

/// Test 5: Discharge type — 3-way disjunction.
/// 1=center, 2=end, 3=full bottom. Value 1 (center).
#[test]
fn test_discharge_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("disch_val", "discharge_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_discharge",
        "discharge_type == 1 || discharge_type == 2 || discharge_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge type 1 (center) is valid 3-way disjunction",
    );
}

/// Test 6: Material — 3-way disjunction.
/// 1=carbon steel, 2=SS304, 3=SS316. Value 2 (SS304).
#[test]
fn test_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "material == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material 2 (SS304) is valid 3-way disjunction");
}

/// Test 7: Fill ratio (x10 %) — fill level as scaled percentage bounded [300, 900].
/// 700 represents 70.0%. Value 700 (70.0% fill ratio).
#[test]
fn test_fill_ratio_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fill_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fill_val", "fill_x10 == 700"));
    ctx.push_obligation(ProofObligation::assert("fill_min", "fill_x10 >= 300"));
    ctx.push_obligation(ProofObligation::assert("fill_max", "fill_x10 <= 900"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fill ratio 70.0% (700 x10) in [300, 900]");
}

/// Test 8: Batch time (min) — mixing cycle duration bounded [2, 120], value 15.
#[test]
fn test_batch_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_time", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bt_val", "batch_time == 15"));
    ctx.push_obligation(ProofObligation::assert("bt_min", "batch_time >= 2"));
    ctx.push_obligation(ProofObligation::assert("bt_max", "batch_time <= 120"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch time 15 min in [2, 120]");
}

/// Test 9: Seal type — 3-way disjunction.
/// 1=packing, 2=mechanical, 3=air purge. Value 2 (mechanical).
#[test]
fn test_seal_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type 2 (mechanical) is valid 3-way disjunction",
    );
}

/// Test 10: Dust collection — boolean flag using i32 with if/else pattern.
/// Flag 1 = dust collection system enabled, which activates extraction (extraction_on = 1).
#[test]
fn test_dust_collection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dust_flag", i32_ty());
    ctx.declare_var_typed("extraction_on", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "dust_flag == 0 || dust_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "dust_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "extraction_def",
        "extraction_on == if dust_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "extraction_active",
        "extraction_on == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dust collection flag enables extraction");
}
