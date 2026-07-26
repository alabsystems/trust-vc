// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial band dryer property verification.
// Encodes key parameters of an industrial band dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Band width (x10 m) — scaled at 0.1 m, bounded [5, 30].
/// 5 represents 0.5 m, 30 represents 3.0 m. Value 15 (1.5 m).
#[test]
fn test_band_width_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("width_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("w_val", "width_x10 == 15"));
    ctx.push_obligation(ProofObligation::assert("w_min", "width_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("w_max", "width_x10 <= 30"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "band width 1.5 m (15 x10) in [5, 30]");
}

/// Test 2: Band length (m) — bounded [5, 50], value 20.
#[test]
fn test_band_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("band_length", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bl_val", "band_length == 20"));
    ctx.push_obligation(ProofObligation::assert("bl_min", "band_length >= 5"));
    ctx.push_obligation(ProofObligation::assert("bl_max", "band_length <= 50"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "band length 20 m in [5, 50]");
}

/// Test 3: Product layer thickness (x10 mm) — scaled at 0.1 mm, bounded [5, 500].
/// 5 represents 0.5 mm, 500 represents 50.0 mm. Value 100 (10.0 mm).
#[test]
fn test_product_layer_thickness_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thickness_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("th_val", "thickness_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert("th_min", "thickness_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("th_max", "thickness_x10 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product layer thickness 10.0 mm (100 x10) in [5, 500]",
    );
}

/// Test 4: Drying temperature (deg C) — bounded [40, 180], value 120.
#[test]
fn test_drying_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dry_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "dry_temp == 120"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "dry_temp >= 40"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "dry_temp <= 180"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying temperature 120 C in [40, 180]");
}

/// Test 5: Throughput (kg/h) — bounded [100, 20000], value 5000.
#[test]
fn test_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput", u32_ty());
    ctx.push_obligation(ProofObligation::assume("thr_val", "throughput == 5000"));
    ctx.push_obligation(ProofObligation::assert("thr_min", "throughput >= 100"));
    ctx.push_obligation(ProofObligation::assert("thr_max", "throughput <= 20000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 5000 kg/h in [100, 20000]");
}

/// Test 6: Band material — 3-way disjunction.
/// 1=stainless-mesh, 2=perforated-plate, 3=solid-belt. Value 2 (perforated-plate).
#[test]
fn test_band_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("band_mat", u32_ty());
    ctx.push_obligation(ProofObligation::assume("bm_val", "band_mat == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_band_mat",
        "band_mat == 1 || band_mat == 2 || band_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "band material 2 (perforated-plate) is valid 3-way disjunction",
    );
}

/// Test 7: Air circulation — 3-way disjunction.
/// 1=through-flow, 2=over-flow, 3=combined. Value 1 (through-flow).
#[test]
fn test_air_circulation_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("air_circ", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ac_val", "air_circ == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_air_circ",
        "air_circ == 1 || air_circ == 2 || air_circ == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air circulation 1 (through-flow) is valid 3-way disjunction",
    );
}

/// Test 8: Number of passes — bounded [1, 5], value 3.
#[test]
fn test_number_of_passes_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("num_passes", u32_ty());
    ctx.push_obligation(ProofObligation::assume("np_val", "num_passes == 3"));
    ctx.push_obligation(ProofObligation::assert("np_min", "num_passes >= 1"));
    ctx.push_obligation(ProofObligation::assert("np_max", "num_passes <= 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of passes 3 in [1, 5]");
}

/// Test 9: Heating medium — 3-way disjunction.
/// 1=steam, 2=thermal-oil, 3=electric. Value 3 (electric).
#[test]
fn test_heating_medium_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_med", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hm_val", "heat_med == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heat_med",
        "heat_med == 1 || heat_med == 2 || heat_med == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating medium 3 (electric) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic moisture control — boolean flag using i32 with if/else pattern.
/// Flag 1 = automatic moisture control enabled, control_active = 1.
#[test]
fn test_automatic_moisture_control_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moisture_flag", i32_ty());
    ctx.declare_var_typed("control_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "moisture_flag == 0 || moisture_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "moisture_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "control_def",
        "control_active == if moisture_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("control_on", "control_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "moisture control flag activates automatic control");
}
