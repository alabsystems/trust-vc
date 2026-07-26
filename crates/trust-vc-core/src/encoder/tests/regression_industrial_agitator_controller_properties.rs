// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial agitator controller property verification.
// Encodes key parameters of an industrial agitator system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Motor power (kW) — agitator drive motor rated power bounded [1, 1000], value 75.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "motor_kw == 75"));
    ctx.push_obligation(ProofObligation::assert("pwr_min", "motor_kw >= 1"));
    ctx.push_obligation(ProofObligation::assert("pwr_max", "motor_kw <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 75 kW in [1, 1000]");
}

/// Test 2: Speed (RPM) — agitator shaft speed bounded [1, 3000], value 120.
#[test]
fn test_speed_rpm_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_rpm == 120"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_rpm >= 1"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_rpm <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed 120 RPM in [1, 3000]");
}

/// Test 3: Impeller type — 4-way disjunction.
/// 1=Rushton turbine, 2=pitched blade, 3=anchor, 4=helical ribbon. Value 2 (pitched blade).
#[test]
fn test_impeller_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("impeller_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("imp_val", "impeller_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_impeller",
        "impeller_type == 1 || impeller_type == 2 || impeller_type == 3 || impeller_type == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "impeller type 2 (pitched blade) is valid 4-way disjunction",
    );
}

/// Test 4: Tank volume (L) — agitator vessel capacity bounded [10, 100000], value 5000.
#[test]
fn test_tank_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tank_liters", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vol_val", "tank_liters == 5000"));
    ctx.push_obligation(ProofObligation::assert("vol_min", "tank_liters >= 10"));
    ctx.push_obligation(ProofObligation::assert("vol_max", "tank_liters <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tank volume 5000 L in [10, 100000]");
}

/// Test 5: Viscosity range (x10 mPa-s) — e.g. 50.0 mPa-s = 500, bounded [1, 100000], value 500.
#[test]
fn test_viscosity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("visc_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("visc_val", "visc_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("visc_min", "visc_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("visc_max", "visc_x10 <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viscosity 50.0 mPa-s (500 x10) in [1, 100000]");
}

/// Test 6: Seal type — 3-way disjunction.
/// 1=mechanical, 2=magnetic drive, 3=lip seal. Value 2 (magnetic drive).
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
        "seal type 2 (magnetic drive) is valid 3-way disjunction",
    );
}

/// Test 7: Material — 3-way disjunction.
/// 1=stainless 316, 2=Hastelloy, 3=glass-lined. Value 1 (stainless 316).
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
    expect_verified(
        &result,
        "material 1 (stainless 316) is valid 3-way disjunction",
    );
}

/// Test 8: Torque limit (Nm) — maximum agitator torque bounded [1, 50000], value 2400.
#[test]
fn test_torque_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_nm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("trq_val", "torque_nm == 2400"));
    ctx.push_obligation(ProofObligation::assert("trq_min", "torque_nm >= 1"));
    ctx.push_obligation(ProofObligation::assert("trq_max", "torque_nm <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "torque limit 2400 Nm in [1, 50000]");
}

/// Test 9: Operating temperature offset +500 (deg C) — bounded [250, 1000].
/// 250 represents -250 C, 1000 represents 500 C. Value 570 (70 C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "temp_offset == 570"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "temp_offset >= 250"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "temp_offset <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 70 C (offset 570) in [250, 1000]");
}

/// Test 10: Overload protection — boolean flag using i32 with if/else pattern.
/// Flag 1 = overload detected, which triggers motor shutdown (shutdown = 1).
#[test]
fn test_overload_protection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("overload_flag", i32_ty());
    ctx.declare_var_typed("motor_shutdown", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "overload_flag == 0 || overload_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "overload_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "shutdown_def",
        "motor_shutdown == if overload_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shutdown_triggered",
        "motor_shutdown == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "overload flag triggers motor shutdown");
}
