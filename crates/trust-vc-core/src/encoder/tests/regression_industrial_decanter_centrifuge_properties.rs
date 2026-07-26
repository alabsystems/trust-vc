// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial decanter centrifuge property verification.
// Encodes key parameters of an industrial decanter centrifuge and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Bowl speed (RPM) — bounded [500, 6000], value 4000.
#[test]
fn test_bowl_speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bowl_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("speed_val", "bowl_speed == 4000"));
    ctx.push_obligation(ProofObligation::assert("speed_min", "bowl_speed >= 500"));
    ctx.push_obligation(ProofObligation::assert("speed_max", "bowl_speed <= 6000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl speed 4000 RPM in [500, 6000]");
}

/// Test 2: Bowl diameter (mm) — bounded [150, 1200], value 500.
#[test]
fn test_bowl_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bowl_dia_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "bowl_dia_mm == 500"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "bowl_dia_mm >= 150"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "bowl_dia_mm <= 1200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl diameter 500 mm in [150, 1200]");
}

/// Test 3: Feed rate (m3/h) — bounded [1, 200], value 30.
#[test]
fn test_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_m3h", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_m3h == 30"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_m3h >= 1"));
    ctx.push_obligation(ProofObligation::assert("feed_max", "feed_m3h <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 30 m3/h in [1, 200]");
}

/// Test 4: Scroll type — 3-way disjunction.
/// 1=single lead, 2=double lead, 3=variable pitch. Value 2 (double lead).
#[test]
fn test_scroll_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("scroll_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("scroll_val", "scroll_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_scroll",
        "scroll_type == 1 || scroll_type == 2 || scroll_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "scroll type 2 (double lead) is valid 3-way disjunction",
    );
}

/// Test 5: Drive type — 3-way disjunction.
/// 1=direct, 2=belt, 3=gearbox. Value 3 (gearbox).
#[test]
fn test_drive_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("drive_val", "drive_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_drive",
        "drive_type == 1 || drive_type == 2 || drive_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type 3 (gearbox) is valid 3-way disjunction");
}

/// Test 6: G-force (x10) — bounded [1000, 50000], value 30000 (3000.0 G).
#[test]
fn test_g_force_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gforce_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gf_val", "gforce_x10 == 30000"));
    ctx.push_obligation(ProofObligation::assert("gf_min", "gforce_x10 >= 1000"));
    ctx.push_obligation(ProofObligation::assert("gf_max", "gforce_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "g-force 3000.0 G (30000 x10) in [1000, 50000]");
}

/// Test 7: Differential speed (RPM) — bounded [1, 100], value 25.
#[test]
fn test_differential_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diff_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("diff_val", "diff_rpm == 25"));
    ctx.push_obligation(ProofObligation::assert("diff_min", "diff_rpm >= 1"));
    ctx.push_obligation(ProofObligation::assert("diff_max", "diff_rpm <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "differential speed 25 RPM in [1, 100]");
}

/// Test 8: Material — 3-way disjunction.
/// 1=SS316, 2=duplex, 3=Hastelloy. Value 1 (SS316).
#[test]
fn test_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material 1 (SS316) is valid 3-way disjunction");
}

/// Test 9: Cake dryness (x10 %) — bounded [100, 700], value 350 (35.0%).
#[test]
fn test_cake_dryness_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dry_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dry_val", "dry_x10 == 350"));
    ctx.push_obligation(ProofObligation::assert("dry_min", "dry_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("dry_max", "dry_x10 <= 700"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cake dryness 35.0% (350 x10) in [100, 700]");
}

/// Test 10: Vibration monitor — boolean flag using i32 with if/else pattern.
/// Flag 1 = vibration monitor enabled, monitor_active = 1.
#[test]
fn test_vibration_monitor_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vib_flag", i32_ty());
    ctx.declare_var_typed("monitor_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "vib_flag == 0 || vib_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "vib_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "monitor_def",
        "monitor_active == if vib_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "monitor_triggered",
        "monitor_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vibration monitor flag enables monitoring");
}
