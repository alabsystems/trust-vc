// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial pelletizer controller property verification.
// Encodes key parameters of an industrial pelletizing system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Throughput (kg/h) — pelletizer production rate bounded [10, 50000], value 1200.
#[test]
fn test_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_kgh", u32_ty());
    ctx.push_obligation(ProofObligation::assume("thr_val", "throughput_kgh == 1200"));
    ctx.push_obligation(ProofObligation::assert("thr_min", "throughput_kgh >= 10"));
    ctx.push_obligation(ProofObligation::assert(
        "thr_max",
        "throughput_kgh <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 1200 kg/h in [10, 50000]");
}

/// Test 2: Pellet diameter (x10 mm) — e.g. 3.0 mm = 30, bounded [5, 100], value 30.
#[test]
fn test_pellet_diameter_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("diam_val", "diam_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("diam_min", "diam_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("diam_max", "diam_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pellet diameter 3.0 mm (30 x10) in [5, 100]");
}

/// Test 3: Cutter speed (RPM) — rotary cutter speed bounded [100, 5000], value 1500.
#[test]
fn test_cutter_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cutter_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cut_val", "cutter_rpm == 1500"));
    ctx.push_obligation(ProofObligation::assert("cut_min", "cutter_rpm >= 100"));
    ctx.push_obligation(ProofObligation::assert("cut_max", "cutter_rpm <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cutter speed 1500 RPM in [100, 5000]");
}

/// Test 4: Pelletizer type — 3-way disjunction.
/// 1=strand, 2=underwater, 3=hot die face. Value 2 (underwater).
#[test]
fn test_pelletizer_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pelletizer_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("type_val", "pelletizer_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_type",
        "pelletizer_type == 1 || pelletizer_type == 2 || pelletizer_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "pelletizer type 2 (underwater) is valid 3-way disjunction",
    );
}

/// Test 5: Die holes — number of extrusion die holes bounded [10, 5000], value 480.
#[test]
fn test_die_holes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("die_holes", u32_ty());
    ctx.push_obligation(ProofObligation::assume("holes_val", "die_holes == 480"));
    ctx.push_obligation(ProofObligation::assert("holes_min", "die_holes >= 10"));
    ctx.push_obligation(ProofObligation::assert("holes_max", "die_holes <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "die holes 480 in [10, 5000]");
}

/// Test 6: Melt temperature (deg C) — bounded [100, 400], value 230.
/// All values positive, no offset needed.
#[test]
fn test_melt_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("melt_temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "melt_temp_c == 230"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "melt_temp_c >= 100"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "melt_temp_c <= 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "melt temperature 230 C in [100, 400]");
}

/// Test 7: Cooling type — 3-way disjunction.
/// 1=air, 2=water bath, 3=spray. Value 2 (water bath).
#[test]
fn test_cooling_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cool_val", "cooling_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_cooling",
        "cooling_type == 1 || cooling_type == 2 || cooling_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "cooling type 2 (water bath) is valid 3-way disjunction",
    );
}

/// Test 8: Blade material — 3-way disjunction.
/// 1=tool steel, 2=carbide, 3=ceramic. Value 3 (ceramic).
#[test]
fn test_blade_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "blade_material == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "blade_material == 1 || blade_material == 2 || blade_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "blade material 3 (ceramic) is valid 3-way disjunction",
    );
}

/// Test 9: Operating pressure (bar) — extrusion system pressure bounded [1, 500], value 85.
#[test]
fn test_operating_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pres_val", "pressure_bar == 85"));
    ctx.push_obligation(ProofObligation::assert("pres_min", "pressure_bar >= 1"));
    ctx.push_obligation(ProofObligation::assert("pres_max", "pressure_bar <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating pressure 85 bar in [1, 500]");
}

/// Test 10: Auto blade gap — boolean flag using i32 with if/else pattern.
/// Flag 1 = automatic blade gap adjustment enabled, which sets gap to optimal 50 (x0.01 mm).
#[test]
fn test_auto_blade_gap_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_gap_flag", i32_ty());
    ctx.declare_var_typed("blade_gap", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "auto_gap_flag == 0 || auto_gap_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "auto_gap_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "gap_def",
        "blade_gap == if auto_gap_flag == 1 { 50 } else { 100 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_gap_optimal",
        "blade_gap == 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto blade gap flag sets optimal gap of 50");
}
