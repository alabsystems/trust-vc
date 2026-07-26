// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial ribbon mixer property verification.
// Encodes key parameters of an industrial ribbon mixer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Trough volume (L) — mixer trough capacity bounded [100, 10000], value 1500.
#[test]
fn test_trough_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trough_l", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "trough_l == 1500"));
    ctx.push_obligation(ProofObligation::assert("vol_min", "trough_l >= 100"));
    ctx.push_obligation(ProofObligation::assert("vol_max", "trough_l <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "trough volume 1500 L in [100, 10000]");
}

/// Test 2: Ribbon speed (RPM) — agitator ribbon rotational speed bounded [5, 100], value 25.
#[test]
fn test_ribbon_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_rpm == 25"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_rpm >= 5"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_rpm <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "ribbon speed 25 RPM in [5, 100]");
}

/// Test 3: Motor power (kW) — drive motor rated power bounded [2, 200], value 37.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "motor_kw == 37"));
    ctx.push_obligation(ProofObligation::assert("pwr_min", "motor_kw >= 2"));
    ctx.push_obligation(ProofObligation::assert("pwr_max", "motor_kw <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 37 kW in [2, 200]");
}

/// Test 4: Fill level (x10 %) — fill level as scaled percentage bounded [300, 900].
/// 700 represents 70.0%. Value 700 (70.0% fill level).
#[test]
fn test_fill_level_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fill_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fill_val", "fill_x10 == 700"));
    ctx.push_obligation(ProofObligation::assert("fill_min", "fill_x10 >= 300"));
    ctx.push_obligation(ProofObligation::assert("fill_max", "fill_x10 <= 900"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fill level 70.0% (700 x10) in [300, 900]");
}

/// Test 5: Mix time (s) — mixing cycle duration bounded [60, 1800], value 300.
#[test]
fn test_mix_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mix_time_s", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mt_val", "mix_time_s == 300"));
    ctx.push_obligation(ProofObligation::assert("mt_min", "mix_time_s >= 60"));
    ctx.push_obligation(ProofObligation::assert("mt_max", "mix_time_s <= 1800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mix time 300 s in [60, 1800]");
}

/// Test 6: Ribbon type — 3-way disjunction.
/// 1=continuous, 2=interrupted, 3=paddle. Value 1 (continuous).
#[test]
fn test_ribbon_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ribbon_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rtype_val", "ribbon_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_ribbon",
        "ribbon_type == 1 || ribbon_type == 2 || ribbon_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ribbon type 1 (continuous) is valid 3-way disjunction",
    );
}

/// Test 7: Discharge type — 3-way disjunction.
/// 1=center, 2=end, 3=bottom. Value 3 (bottom).
#[test]
fn test_discharge_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("disch_val", "discharge_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_discharge",
        "discharge_type == 1 || discharge_type == 2 || discharge_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge type 3 (bottom) is valid 3-way disjunction",
    );
}

/// Test 8: Trough material — 3-way disjunction.
/// 1=carbon steel, 2=stainless steel, 3=hastelloy. Value 2 (stainless steel).
#[test]
fn test_trough_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("trough_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "trough_material == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "trough_material == 1 || trough_material == 2 || trough_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "trough material 2 (stainless steel) is valid 3-way disjunction",
    );
}

/// Test 9: Batch weight (kg) — maximum batch weight bounded [50, 5000], value 800.
#[test]
fn test_batch_weight_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_kg", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bw_val", "batch_kg == 800"));
    ctx.push_obligation(ProofObligation::assert("bw_min", "batch_kg >= 50"));
    ctx.push_obligation(ProofObligation::assert("bw_max", "batch_kg <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch weight 800 kg in [50, 5000]");
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
