// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial flash dryer controller property verification.
// Encodes key parameters of an industrial flash dryer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Inlet air temperature offset +500 (deg C) — bounded [800, 1100].
/// 800 represents 300 C, 1100 represents 600 C. Value 900 (400 C).
#[test]
fn test_flash_dryer_inlet_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("inlet_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "inlet_val",
        "inlet_temp_offset == 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_min",
        "inlet_temp_offset >= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "inlet_max",
        "inlet_temp_offset <= 1100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "inlet air temp 400 C (offset 900) in [800, 1100]");
}

/// Test 2: Outlet air temperature offset +500 (deg C) — bounded [580, 650].
/// 580 represents 80 C, 650 represents 150 C. Value 610 (110 C).
#[test]
fn test_flash_dryer_outlet_air_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("outlet_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "outlet_val",
        "outlet_temp_offset == 610",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_min",
        "outlet_temp_offset >= 580",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "outlet_max",
        "outlet_temp_offset <= 650",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "outlet air temp 110 C (offset 610) in [580, 650]");
}

/// Test 3: Feed rate (x10 kg/h) — scaled at 0.1 kg/h, bounded [50, 50000].
/// 50 represents 5.0 kg/h, 50000 represents 5000.0 kg/h. Value 8000 (800.0 kg/h).
#[test]
fn test_flash_dryer_feed_rate_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_x10 == 8000"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_x10 >= 50"));
    ctx.push_obligation(ProofObligation::assert("feed_max", "feed_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 800.0 kg/h (8000 x10) in [50, 50000]");
}

/// Test 4: Air velocity (x10 m/s) — scaled at 0.1 m/s, bounded [100, 400].
/// 100 represents 10.0 m/s, 400 represents 40.0 m/s. Value 250 (25.0 m/s).
#[test]
fn test_flash_dryer_air_velocity_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("velocity_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("vel_val", "velocity_x10 == 250"));
    ctx.push_obligation(ProofObligation::assert("vel_min", "velocity_x10 >= 100"));
    ctx.push_obligation(ProofObligation::assert("vel_max", "velocity_x10 <= 400"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "air velocity 25.0 m/s (250 x10) in [100, 400]");
}

/// Test 5: Evaporation rate (kg/h) — bounded [100, 10000], value 2500.
#[test]
fn test_flash_dryer_evaporation_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_rate", u32_ty());
    ctx.push_obligation(ProofObligation::assume("evap_val", "evap_rate == 2500"));
    ctx.push_obligation(ProofObligation::assert("evap_min", "evap_rate >= 100"));
    ctx.push_obligation(ProofObligation::assert("evap_max", "evap_rate <= 10000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evaporation rate 2500 kg/h in [100, 10000]");
}

/// Test 6: Duct diameter (mm) — bounded [300, 2000], value 800.
#[test]
fn test_flash_dryer_duct_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("duct_dia", u32_ty());
    ctx.push_obligation(ProofObligation::assume("duct_val", "duct_dia == 800"));
    ctx.push_obligation(ProofObligation::assert("duct_min", "duct_dia >= 300"));
    ctx.push_obligation(ProofObligation::assert("duct_max", "duct_dia <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "duct diameter 800 mm in [300, 2000]");
}

/// Test 7: Feed type — 3-way disjunction.
/// 1=filter cake, 2=paste, 3=slurry. Value 1 (filter cake).
#[test]
fn test_flash_dryer_feed_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ft_val", "feed_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_feed_type",
        "feed_type == 1 || feed_type == 2 || feed_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "feed type 1 (filter cake) is valid 3-way disjunction",
    );
}

/// Test 8: Collector type — 3-way disjunction.
/// 1=cyclone, 2=bag filter, 3=scrubber. Value 2 (bag filter).
#[test]
fn test_flash_dryer_collector_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("collector_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("coll_val", "collector_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_collector",
        "collector_type == 1 || collector_type == 2 || collector_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "collector type 2 (bag filter) is valid 3-way disjunction",
    );
}

/// Test 9: Residence time (x10 s) — scaled at 0.1 s, bounded [5, 300].
/// 5 represents 0.5 s, 300 represents 30.0 s. Value 20 (2.0 s).
#[test]
fn test_flash_dryer_residence_time_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("residence_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("res_val", "residence_x10 == 20"));
    ctx.push_obligation(ProofObligation::assert("res_min", "residence_x10 >= 5"));
    ctx.push_obligation(ProofObligation::assert("res_max", "residence_x10 <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "residence time 2.0 s (20 x10) in [5, 300]");
}

/// Test 10: Explosion venting — boolean flag using i32 with if/else pattern.
/// Flag 1 = explosion venting installed, vent_active = 1.
#[test]
fn test_flash_dryer_explosion_venting_boolean_flag() {
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
    expect_verified(&result, "explosion venting flag activates vent system");
}
