// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial centrifuge controller property verification.
// Encodes key parameters of an industrial centrifuge system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Max speed (RPM) — bounded [100, 30000], value 15000.
#[test]
fn test_max_speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "max_rpm == 15000"));
    ctx.push_obligation(ProofObligation::assert("rpm_min", "max_rpm >= 100"));
    ctx.push_obligation(ProofObligation::assert("rpm_max", "max_rpm <= 30000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max speed 15000 RPM in [100, 30000]");
}

/// Test 2: Bowl diameter (mm) — bounded [100, 2000], value 600.
#[test]
fn test_bowl_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bowl_dia_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "bowl_dia_mm == 600"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "bowl_dia_mm >= 100"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "bowl_dia_mm <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl diameter 600 mm in [100, 2000]");
}

/// Test 3: Centrifuge type — 4-way disjunction.
/// 1=decanter, 2=disc stack, 3=tubular, 4=basket. Value 2 (disc stack).
#[test]
fn test_centrifuge_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("centrifuge_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ctype_val", "centrifuge_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_centrifuge_type",
        "centrifuge_type == 1 || centrifuge_type == 2 || centrifuge_type == 3 || centrifuge_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "centrifuge type 2 (disc stack) is valid 4-way disjunction",
    );
}

/// Test 4: Motor power (kW) — bounded [1, 500], value 75.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("motor_val", "motor_kw == 75"));
    ctx.push_obligation(ProofObligation::assert("motor_min", "motor_kw >= 1"));
    ctx.push_obligation(ProofObligation::assert("motor_max", "motor_kw <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 75 kW in [1, 500]");
}

/// Test 5: G-force (x10) — e.g., 5000.0g encoded as 50000, bounded [100, 200000].
/// Value 50000 represents 5000.0g.
#[test]
fn test_g_force_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("g_force_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gf_val", "g_force_x10 == 50000"));
    ctx.push_obligation(ProofObligation::assert("gf_min", "g_force_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("gf_max", "g_force_x10 <= 200000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "g-force 5000.0g (50000 x10) in [100, 200000]");
}

/// Test 6: Feed rate (L/h) — bounded [10, 100000], value 5000.
#[test]
fn test_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_lph", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_lph == 5000"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_lph >= 10"));
    ctx.push_obligation(ProofObligation::assert("feed_max", "feed_lph <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 5000 L/h in [10, 100000]");
}

/// Test 7: Separation type — 3-way disjunction.
/// 1=liquid-liquid, 2=solid-liquid, 3=three-phase. Value 3 (three-phase).
#[test]
fn test_separation_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sep_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sep_val", "sep_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_separation",
        "sep_type == 1 || sep_type == 2 || sep_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "separation type 3 (three-phase) is valid 3-way disjunction",
    );
}

/// Test 8: Operating temperature offset +500 (deg C) — bounded [250, 800].
/// 250 represents -250 C, 800 represents 300 C. Value 520 (20 C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("op_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "op_temp_offset == 520"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "op_temp_offset >= 250"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "op_temp_offset <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 20 C (offset 520) in [250, 800]");
}

/// Test 9: Vibration limit (x100 mm/s) — e.g., 2.50 mm/s encoded as 250, bounded [10, 1000].
/// Value 250 represents 2.50 mm/s.
#[test]
fn test_vibration_limit_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vib_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vib_val", "vib_x100 == 250"));
    ctx.push_obligation(ProofObligation::assert("vib_min", "vib_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert("vib_max", "vib_x100 <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vibration limit 2.50 mm/s (250 x100) in [10, 1000]",
    );
}

/// Test 10: Imbalance detection — boolean flag using i32 with if/else pattern.
/// Flag 1 = imbalance detected, which triggers emergency stop (e_stop = 1).
#[test]
fn test_imbalance_detection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imbalance_flag", i32_ty());
    ctx.declare_var_typed("e_stop", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "imbalance_flag == 0 || imbalance_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "imbalance_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "estop_def",
        "e_stop == if imbalance_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("estop_triggered", "e_stop == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "imbalance flag triggers emergency stop");
}
