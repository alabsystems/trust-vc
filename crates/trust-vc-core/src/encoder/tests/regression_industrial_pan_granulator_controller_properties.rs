// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial pan granulator controller property verification.
// Encodes key parameters of a pan (disc) granulator system and verifies
// that they satisfy bounded, scaled, disjunctive, and boolean-flag constraints.

/// Test 1: Pan diameter (mm) — bounded [1000, 6000], value 3500.
#[test]
fn test_pan_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pan_dia_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dia_val", "pan_dia_mm == 3500"));
    ctx.push_obligation(ProofObligation::assert("dia_min", "pan_dia_mm >= 1000"));
    ctx.push_obligation(ProofObligation::assert("dia_max", "pan_dia_mm <= 6000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pan diameter 3500 mm in [1000, 6000]");
}

/// Test 2: Pan tilt angle (x10 degrees) — 0.1 deg resolution, bounded [300, 600].
/// Value 450 represents 45.0 degrees.
#[test]
fn test_pan_tilt_angle_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tilt_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tilt_val", "tilt_x10 == 450"));
    ctx.push_obligation(ProofObligation::assert("tilt_min", "tilt_x10 >= 300"));
    ctx.push_obligation(ProofObligation::assert("tilt_max", "tilt_x10 <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pan tilt angle 45.0 deg (450 x10) in [300, 600]");
}

/// Test 3: Rotation speed (x10 RPM) — 0.1 RPM resolution, bounded [50, 200].
/// Value 85 represents 8.5 RPM.
#[test]
fn test_rotation_speed_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_x10 == 85"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_x10 <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 8.5 RPM (85 x10) in [50, 200]");
}

/// Test 4: Motor power (kW) — bounded [5, 200], value 55.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "motor_kw == 55"));
    ctx.push_obligation(ProofObligation::assert("pwr_min", "motor_kw >= 5"));
    ctx.push_obligation(ProofObligation::assert("pwr_max", "motor_kw <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 55 kW in [5, 200]");
}

/// Test 5: Throughput (kg/h) — bounded [100, 10000], value 2500.
#[test]
fn test_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_kgh", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tput_val",
        "throughput_kgh == 2500",
    ));
    ctx.push_obligation(ProofObligation::assert("tput_min", "throughput_kgh >= 100"));
    ctx.push_obligation(ProofObligation::assert(
        "tput_max",
        "throughput_kgh <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 2500 kg/h in [100, 10000]");
}

/// Test 6: Spray type — 3-way disjunction.
/// 1=binder, 2=coating, 3=water. Value 1 (binder).
#[test]
fn test_spray_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spray_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spray_val", "spray_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_spray_type",
        "spray_type == 1 || spray_type == 2 || spray_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spray type 1 (binder) is valid 3-way disjunction");
}

/// Test 7: Pan rim height (mm) — bounded [200, 800], value 450.
#[test]
fn test_pan_rim_height_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rim_height_mm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rim_val", "rim_height_mm == 450"));
    ctx.push_obligation(ProofObligation::assert("rim_min", "rim_height_mm >= 200"));
    ctx.push_obligation(ProofObligation::assert("rim_max", "rim_height_mm <= 800"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pan rim height 450 mm in [200, 800]");
}

/// Test 8: Product type — 3-way disjunction.
/// 1=fertilizer, 2=ore, 3=chemical. Value 2 (ore).
#[test]
fn test_product_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("product_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("prod_val", "product_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_product_type",
        "product_type == 1 || product_type == 2 || product_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "product type 2 (ore) is valid 3-way disjunction");
}

/// Test 9: Granule size (x10 mm) — 0.1 mm resolution, bounded [10, 100].
/// Value 35 represents 3.5 mm.
#[test]
fn test_granule_size_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("granule_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("gran_val", "granule_x10 == 35"));
    ctx.push_obligation(ProofObligation::assert("gran_min", "granule_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("gran_max", "granule_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "granule size 3.5 mm (35 x10) in [10, 100]");
}

/// Test 10: Dust suppression — boolean flag using i32 with if/else pattern.
/// Flag 1 = dust detected, which activates suppression spray (spray_active = 1).
#[test]
fn test_dust_suppression_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dust_flag", i32_ty());
    ctx.declare_var_typed("spray_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "dust_flag == 0 || dust_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "dust_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "spray_def",
        "spray_active == if dust_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spray_triggered",
        "spray_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dust flag triggers suppression spray");
}
