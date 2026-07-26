// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial desiccant dryer property verification.
// Encodes key parameters of an industrial desiccant air dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Flow capacity (m³/min) — compressed air flow bounded [1, 500], value 120.
#[test]
fn test_flow_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_m3min", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_m3min == 120"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "flow_m3min >= 1"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "flow_m3min <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow capacity 120 m3/min in [1, 500]");
}

/// Test 2: Dew point offset +500 (deg C) — bounded [350, 500].
/// 350 represents -150 C, 500 represents 0 C. Value 460 (-40 C). Value 430 (-70 C).
/// Using value 460 for a standard -40 C pressure dew point.
#[test]
fn test_dew_point_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dewpoint_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dp_val", "dewpoint_offset == 460"));
    ctx.push_obligation(ProofObligation::assert("dp_min", "dewpoint_offset >= 350"));
    ctx.push_obligation(ProofObligation::assert("dp_max", "dewpoint_offset <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dew point -40 C (offset 460) in [350, 500]");
}

/// Test 3: Desiccant type — 3-way disjunction.
/// 1=silica gel, 2=activated alumina, 3=molecular sieve. Value 2 (activated alumina).
#[test]
fn test_desiccant_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("desiccant_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("des_val", "desiccant_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_desiccant",
        "desiccant_type == 1 || desiccant_type == 2 || desiccant_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "desiccant type 2 (activated alumina) is valid 3-way disjunction",
    );
}

/// Test 4: Regeneration type — 3-way disjunction.
/// 1=heatless, 2=heated, 3=blower purge. Value 1 (heatless).
#[test]
fn test_regeneration_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("regen_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("regen_val", "regen_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_regen",
        "regen_type == 1 || regen_type == 2 || regen_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "regeneration type 1 (heatless) is valid 3-way disjunction",
    );
}

/// Test 5: Inlet pressure (kPa) — compressed air inlet bounded [300, 1600], value 700.
#[test]
fn test_inlet_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_kpa", u32_ty());
    ctx.push_obligation(ProofObligation::assume("inlet_val", "inlet_kpa == 700"));
    ctx.push_obligation(ProofObligation::assert("inlet_min", "inlet_kpa >= 300"));
    ctx.push_obligation(ProofObligation::assert("inlet_max", "inlet_kpa <= 1600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet pressure 700 kPa in [300, 1600]");
}

/// Test 6: Cycle time (min) — half-cycle switching time bounded [2, 60], value 5.
#[test]
fn test_cycle_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cycle_min", u32_ty());
    ctx.push_obligation(ProofObligation::assume("cycle_val", "cycle_min == 5"));
    ctx.push_obligation(ProofObligation::assert("cycle_lo", "cycle_min >= 2"));
    ctx.push_obligation(ProofObligation::assert("cycle_hi", "cycle_min <= 60"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle time 5 min in [2, 60]");
}

/// Test 7: Purge air (x10 %) — purge consumption as scaled percentage bounded [0, 300].
/// 150 represents 15.0%. Value 150 (15.0% purge air consumption).
#[test]
fn test_purge_air_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("purge_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("purge_val", "purge_x10 == 150"));
    ctx.push_obligation(ProofObligation::assert("purge_min", "purge_x10 >= 0"));
    ctx.push_obligation(ProofObligation::assert("purge_max", "purge_x10 <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "purge air 15.0% (150 x10) in [0, 300]");
}

/// Test 8: Tower count — 2-way disjunction.
/// 1=twin tower, 2=triple tower. Value 1 (twin tower).
#[test]
fn test_tower_count_two_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tower_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tower_val", "tower_count == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_tower",
        "tower_count == 1 || tower_count == 2",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tower count 1 (twin tower) is valid 2-way disjunction",
    );
}

/// Test 9: Operating temperature offset +500 (deg C) — bounded [450, 600].
/// 450 represents -50 C, 600 represents 100 C. Value 535 (35 C).
#[test]
fn test_operating_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("op_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "op_temp_offset == 535"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "op_temp_offset >= 450"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "op_temp_offset <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating temp 35 C (offset 535) in [450, 600]");
}

/// Test 10: Dew point alarm — boolean flag using i32 with if/else pattern.
/// Flag 1 = dew point exceeded threshold, which triggers alarm (alarm_active = 1).
#[test]
fn test_dew_point_alarm_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dp_alarm_flag", i32_ty());
    ctx.declare_var_typed("alarm_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "dp_alarm_flag == 0 || dp_alarm_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "dp_alarm_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "alarm_def",
        "alarm_active == if dp_alarm_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "alarm_triggered",
        "alarm_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dew point alarm flag triggers alarm");
}
