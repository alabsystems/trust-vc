// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Wire drawing controller property verification.
// Encodes key parameters of a multi-die wire drawing machine and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Wire diameter (×100 mm) — e.g., 2.50 mm = 250, bounded [10, 5000].
#[test]
fn test_wire_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diameter_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wd_val", "diameter_x100 == 250"));
    ctx.push_obligation(ProofObligation::assert("wd_min", "diameter_x100 >= 10"));
    ctx.push_obligation(ProofObligation::assert("wd_max", "diameter_x100 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wire diameter 2.50 mm (250 x100) in [10, 5000]");
}

/// Test 2: Drawing speed (m/min) — bounded [1, 3000], value 1200.
#[test]
fn test_drawing_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("draw_speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ds_val", "draw_speed == 1200"));
    ctx.push_obligation(ProofObligation::assert("ds_min", "draw_speed >= 1"));
    ctx.push_obligation(ProofObligation::assert("ds_max", "draw_speed <= 3000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drawing speed 1200 m/min in [1, 3000]");
}

/// Test 3: Material type — 4-way disjunction.
/// 1=copper, 2=aluminum, 3=steel, 4=stainless. Value 3 (steel).
#[test]
fn test_material_type_four_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mt_val", "material == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "material == 1 || material == 2 || material == 3 || material == 4",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material 3 (steel) is valid 4-way disjunction");
}

/// Test 4: Die count — bounded [1, 30], value 12.
#[test]
fn test_die_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("die_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dc_val", "die_count == 12"));
    ctx.push_obligation(ProofObligation::assert("dc_min", "die_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("dc_max", "die_count <= 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "die count 12 in [1, 30]");
}

/// Test 5: Motor power (kW) — bounded [1, 2000], value 750.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mp_val", "motor_kw == 750"));
    ctx.push_obligation(ProofObligation::assert("mp_min", "motor_kw >= 1"));
    ctx.push_obligation(ProofObligation::assert("mp_max", "motor_kw <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 750 kW in [1, 2000]");
}

/// Test 6: Reduction ratio (×10 %) — e.g., 20.0% = 200, bounded [50, 450].
#[test]
fn test_reduction_ratio_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reduction_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rr_val", "reduction_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert("rr_min", "reduction_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("rr_max", "reduction_x10 <= 450"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reduction ratio 20.0% (200 x10) in [50, 450]");
}

/// Test 7: Lubricant type — 3-way disjunction.
/// 1=dry soap, 2=wet, 3=emulsion. Value 2 (wet).
#[test]
fn test_lubricant_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lubricant", u32_ty());
    ctx.push_obligation(ProofObligation::assume("lt_val", "lubricant == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_lubricant",
        "lubricant == 1 || lubricant == 2 || lubricant == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lubricant 2 (wet) is valid 3-way disjunction");
}

/// Test 8: Tension (N) — bounded [10, 100000], value 4500.
#[test]
fn test_tension_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tension_n", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tn_val", "tension_n == 4500"));
    ctx.push_obligation(ProofObligation::assert("tn_min", "tension_n >= 10"));
    ctx.push_obligation(ProofObligation::assert("tn_max", "tension_n <= 100000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tension 4500 N in [10, 100000]");
}

/// Test 9: Capstan speed synchronization — 3-way disjunction.
/// 1=master-slave, 2=dancer, 3=torque. Value 1 (master-slave).
#[test]
fn test_capstan_sync_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("capstan_sync", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cs_val", "capstan_sync == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_sync",
        "capstan_sync == 1 || capstan_sync == 2 || capstan_sync == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capstan sync 1 (master-slave) is valid 3-way disjunction",
    );
}

/// Test 10: Break detection — boolean flag (i32_ty).
/// Wire break sensor is active (1) when break detected.
#[test]
fn test_break_detection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wire_tension", u32_ty());
    ctx.declare_var_typed("min_tension", u32_ty());
    ctx.declare_var_typed("break_detected", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wt", "wire_tension == 5"));
    ctx.push_obligation(ProofObligation::assume("mt", "min_tension == 50"));
    ctx.push_obligation(ProofObligation::assume(
        "bd_def",
        "break_detected == if wire_tension < min_tension { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("yes", "break_detected == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "wire drawing: tension 5 N < 50 N min -> break detected",
    );
}
