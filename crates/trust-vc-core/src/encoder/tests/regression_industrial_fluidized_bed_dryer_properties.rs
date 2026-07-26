// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial fluidized bed dryer property verification.
// Encodes key parameters of an industrial fluidized bed dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Bed capacity (kg) — bounded [5, 2000], value 500.
#[test]
fn test_bed_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bed_capacity_kg", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cap_val", "bed_capacity_kg == 500"));
    ctx.push_obligation(ProofObligation::assert("cap_min", "bed_capacity_kg >= 5"));
    ctx.push_obligation(ProofObligation::assert(
        "cap_max",
        "bed_capacity_kg <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bed capacity 500 kg in [5, 2000]");
}

/// Test 2: Inlet air temperature (deg C) — bounded [40, 200], value 80.
#[test]
fn test_inlet_air_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_c", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "inlet_temp_c == 80"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "inlet_temp_c >= 40"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "inlet_temp_c <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet air temperature 80 C in [40, 200]");
}

/// Test 3: Air flow rate (x10 m3/min) — bounded [10, 5000].
/// 10 represents 1.0 m3/min, 5000 represents 500.0 m3/min. Value 750 (75.0 m3/min).
#[test]
fn test_air_flow_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("airflow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "airflow_x10 == 750"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "airflow_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "airflow_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air flow rate 75.0 m3/min (750 x10) in [10, 5000]");
}

/// Test 4: Product moisture target (x10 %) — bounded [1, 100].
/// 1 represents 0.1%, 100 represents 10.0%. Value 30 (3.0%).
#[test]
fn test_product_moisture_target_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("moisture_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("moist_val", "moisture_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("moist_min", "moisture_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("moist_max", "moisture_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "product moisture target 3.0% (30 x10) in [1, 100]");
}

/// Test 5: Drying time (minutes) — bounded [5, 240], value 45.
#[test]
fn test_drying_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drying_time_min", u32_ty());
    ctx.push_obligation(ProofObligation::assume("time_val", "drying_time_min == 45"));
    ctx.push_obligation(ProofObligation::assert("time_lo", "drying_time_min >= 5"));
    ctx.push_obligation(ProofObligation::assert("time_hi", "drying_time_min <= 240"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drying time 45 min in [5, 240]");
}

/// Test 6: Fluidization method — 3-way disjunction.
/// 1=top-spray, 2=bottom-spray, 3=tangential-spray. Value 2 (bottom-spray).
#[test]
fn test_fluidization_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fluid_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("method_val", "fluid_method == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_method",
        "fluid_method == 1 || fluid_method == 2 || fluid_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "fluidization method 2 (bottom-spray) is valid 3-way disjunction",
    );
}

/// Test 7: Filter type — 3-way disjunction.
/// 1=bag, 2=cartridge, 3=sintered-plate. Value 1 (bag).
#[test]
fn test_filter_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("filter_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("filter_val", "filter_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_filter",
        "filter_type == 1 || filter_type == 2 || filter_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "filter type 1 (bag) is valid 3-way disjunction");
}

/// Test 8: Air distribution plate — 3-way disjunction.
/// 1=perforated, 2=gill, 3=bubble-cap. Value 3 (bubble-cap).
#[test]
fn test_air_distribution_plate_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plate_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("plate_val", "plate_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_plate",
        "plate_type == 1 || plate_type == 2 || plate_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "air distribution plate 3 (bubble-cap) is valid 3-way disjunction",
    );
}

/// Test 9: Explosion vent — boolean flag using i32 with if/else pattern.
/// Flag 1 = explosion vent installed, which enables safety compliance (vent_active = 1).
#[test]
fn test_explosion_vent_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vent_flag", i32_ty());
    ctx.declare_var_typed("vent_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "vent_flag == 0 || vent_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "vent_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vent_def",
        "vent_active == if vent_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("vent_enabled", "vent_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "explosion vent flag enables safety compliance");
}

/// Test 10: Batch weight (x10 kg) — bounded [10, 20000].
/// 10 represents 1.0 kg, 20000 represents 2000.0 kg. Value 5000 (500.0 kg).
#[test]
fn test_batch_weight_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("batch_wt_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wt_val", "batch_wt_x10 == 5000"));
    ctx.push_obligation(ProofObligation::assert("wt_min", "batch_wt_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("wt_max", "batch_wt_x10 <= 20000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "batch weight 500.0 kg (5000 x10) in [10, 20000]");
}
