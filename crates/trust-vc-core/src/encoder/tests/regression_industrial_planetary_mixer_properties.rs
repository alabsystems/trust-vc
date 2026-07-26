// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial planetary mixer property verification.
// Encodes key parameters of an industrial planetary mixer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Bowl capacity (L) — mixer bowl volume bounded [5, 2000], value 500.
#[test]
fn test_bowl_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "cap == 500"));
    ctx.push_obligation(ProofObligation::assert("cap_min", "cap >= 5"));
    ctx.push_obligation(ProofObligation::assert("cap_max", "cap <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl capacity 500 L in [5, 2000]");
}

/// Test 2: Orbital speed (RPM) — orbital arm rotational speed bounded [10, 200], value 60.
#[test]
fn test_orbital_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("orb_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("orb_val", "orb_speed == 60"));
    ctx.push_obligation(ProofObligation::assert("orb_min", "orb_speed >= 10"));
    ctx.push_obligation(ProofObligation::assert("orb_max", "orb_speed <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "orbital speed 60 RPM in [10, 200]");
}

/// Test 3: Planetary speed (RPM) — blade planetary rotational speed bounded [20, 500], value 120.
#[test]
fn test_planetary_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plan_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("plan_val", "plan_speed == 120"));
    ctx.push_obligation(ProofObligation::assert("plan_min", "plan_speed >= 20"));
    ctx.push_obligation(ProofObligation::assert("plan_max", "plan_speed <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "planetary speed 120 RPM in [20, 500]");
}

/// Test 4: Motor power x10 (kW) — drive motor rated power scaled x10, bounded [10, 5000].
/// 750 represents 75.0 kW. Value 750 (75.0 kW).
#[test]
fn test_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pow_val", "pow_x10 == 750"));
    ctx.push_obligation(ProofObligation::assert("pow_min", "pow_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("pow_max", "pow_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 75.0 kW (750 x10) in [10, 5000]");
}

/// Test 5: Mixing torque x10 (N-m) — torque scaled x10, bounded [50, 50000].
/// 5000 represents 500.0 N-m. Value 5000 (500.0 N-m).
#[test]
fn test_torque_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torq_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("torq_val", "torq_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert("torq_min", "torq_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("torq_max", "torq_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mixing torque 500.0 N-m (5000 x10) in [50, 50000]");
}

/// Test 6: Process vacuum x10 (mbar) — vacuum level scaled x10, bounded [1, 10000].
/// 500 represents 50.0 mbar. Value 500 (50.0 mbar).
#[test]
fn test_vacuum_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vac_val", "vac_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("vac_min", "vac_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("vac_max", "vac_x10 <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "process vacuum 50.0 mbar (500 x10) in [1, 10000]");
}

/// Test 7: Blade type — 3-way disjunction.
/// 1=anchor, 2=helical, 3=butterfly. Value 1 (anchor).
#[test]
fn test_blade_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("blade_val", "blade_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_blade",
        "blade_type == 1 || blade_type == 2 || blade_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blade type 1 (anchor) is valid 3-way disjunction");
}

/// Test 8: Seal type — 3-way disjunction.
/// 1=mechanical, 2=lip, 3=inflatable. Value 2 (lip).
#[test]
fn test_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("seal_val", "seal_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_seal",
        "seal_type == 1 || seal_type == 2 || seal_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seal type 2 (lip) is valid 3-way disjunction");
}

/// Test 9: Vessel material — 3-way disjunction.
/// 1=stainless-304, 2=stainless-316, 3=hastelloy. Value 2 (stainless-316).
#[test]
fn test_vessel_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vessel_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "vessel_material == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "vessel_material == 1 || vessel_material == 2 || vessel_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vessel material 2 (stainless-316) is valid 3-way disjunction",
    );
}

/// Test 10: Jacketed flag — boolean flag using i32 with if/else pattern.
/// Flag 1 = jacket present, which enables thermal control (thermal_on = 1).
#[test]
fn test_jacketed_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket", i32_ty());
    ctx.declare_var_typed("thermal_on", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "jacket == 0 || jacket == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "jacket == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "thermal_def",
        "thermal_on == if jacket == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("thermal_active", "thermal_on == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jacketed flag enables thermal control");
}
