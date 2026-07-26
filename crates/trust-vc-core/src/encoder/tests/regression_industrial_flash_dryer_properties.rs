// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial flash dryer (pneumatic dryer) property verification.
// Encodes key parameters of an industrial flash dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Air inlet temperature offset +100 (deg C) — bounded [200, 900].
/// 200 represents 100 C, 900 represents 800 C. Value 500 (400 C).
#[test]
fn test_flash_dryer_air_inlet_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_val",
        "inlet_temp_offset == 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_min",
        "inlet_temp_offset >= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_max",
        "inlet_temp_offset <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air inlet temp 400 C (offset 500) in [200, 900]");
}

/// Test 2: Air velocity (x10 m/s) — scaled at 0.1 m/s, bounded [50, 500].
/// 50 represents 5.0 m/s, 500 represents 50.0 m/s. Value 200 (20.0 m/s).
#[test]
fn test_flash_dryer_air_velocity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vel_val", "velocity_x10 == 200"));
    ctx.push_obligation(ProofObligation::assert("vel_min", "velocity_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("vel_max", "velocity_x10 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air velocity 20.0 m/s (200 x10) in [50, 500]");
}

/// Test 3: Evaporation rate (x10 kg/h) — scaled at 0.1 kg/h, bounded [100, 500000].
/// 100 represents 10.0 kg/h, 500000 represents 50000.0 kg/h. Value 10000 (1000.0 kg/h).
#[test]
fn test_flash_dryer_evaporation_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("evap_val", "evap_x10 == 10000"));
    ctx.push_obligation(ProofObligation::assert("evap_min", "evap_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("evap_max", "evap_x10 <= 500000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "evaporation rate 1000.0 kg/h (10000 x10) in [100, 500000]",
    );
}

/// Test 4: Duct diameter (x10 mm) — scaled at 0.1 mm, bounded [100, 30000].
/// 100 represents 10.0 mm, 30000 represents 3000.0 mm. Value 8000 (800.0 mm).
#[test]
fn test_flash_dryer_duct_diameter_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("duct_dia_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("duct_val", "duct_dia_x10 == 8000"));
    ctx.push_obligation(ProofObligation::assert("duct_min", "duct_dia_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("duct_max", "duct_dia_x10 <= 30000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "duct diameter 800.0 mm (8000 x10) in [100, 30000]");
}

/// Test 5: Residence time (x100 sec) — scaled at 0.01 sec, bounded [1, 500].
/// 1 represents 0.01 sec, 500 represents 5.00 sec. Value 20 (0.20 sec).
#[test]
fn test_flash_dryer_residence_time_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_time_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "res_time_x100 == 20"));
    ctx.push_obligation(ProofObligation::assert("res_min", "res_time_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert("res_max", "res_time_x100 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time 0.20 sec (20 x100) in [1, 500]");
}

/// Test 6: Number of drying stages — bounded [1, 5], value 1.
#[test]
fn test_flash_dryer_number_of_stages_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stages", u32_ty());
    ctx.push_obligation(ProofObligation::assume("stg_val", "stages == 1"));
    ctx.push_obligation(ProofObligation::assert("stg_min", "stages >= 1"));
    ctx.push_obligation(ProofObligation::assert("stg_max", "stages <= 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of stages 1 in [1, 5]");
}

/// Test 7: Feed method — 3-way disjunction.
/// 1=screw, 2=venturi, 3=disperser. Value 3 (disperser).
#[test]
fn test_flash_dryer_feed_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("fm_val", "feed_method == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_feed",
        "feed_method == 1 || feed_method == 2 || feed_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "feed method 3 (disperser) is valid 3-way disjunction",
    );
}

/// Test 8: Separator type — 3-way disjunction.
/// 1=cyclone, 2=bag-filter, 3=wet-scrubber. Value 1 (cyclone).
#[test]
fn test_flash_dryer_separator_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("separator_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("sep_val", "separator_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_separator",
        "separator_type == 1 || separator_type == 2 || separator_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "separator type 1 (cyclone) is valid 3-way disjunction",
    );
}

/// Test 9: Heating source — 3-way disjunction.
/// 1=direct-gas, 2=indirect-steam, 3=indirect-thermal-oil. Value 1 (direct-gas).
#[test]
fn test_flash_dryer_heating_source_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating_source", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hs_val", "heating_source == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heating",
        "heating_source == 1 || heating_source == 2 || heating_source == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating source 1 (direct-gas) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic temperature control — boolean flag using i32 with if/else pattern.
/// Flag 1 = automatic temperature control enabled, ctrl_active = 1.
#[test]
fn test_flash_dryer_auto_temp_control_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl_flag", i32_ty());
    ctx.declare_var_typed("ctrl_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "ctrl_flag == 0 || ctrl_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "ctrl_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_def",
        "ctrl_active == if ctrl_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ctrl_enabled", "ctrl_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto temp control flag activates temperature controller",
    );
}
