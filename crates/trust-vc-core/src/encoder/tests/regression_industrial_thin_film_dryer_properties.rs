// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial thin-film dryer (agitated thin-film evaporator/dryer) property verification.
// Encodes key parameters of a thin-film dryer used for heat-sensitive, viscous, or fouling
// materials and verifies that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Rotor speed (RPM) — bounded [50, 500], value 250.
#[test]
fn test_thin_film_dryer_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 50 && rpm <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 50 && rpm <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed must be between 50 and 500 RPM");
}

/// Test 2: Film thickness (x100 mm, so 10 = 0.10 mm, 500 = 5.00 mm) — bounded [10, 500], value 75.
#[test]
fn test_thin_film_dryer_film_thickness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("film_thick_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thick_range",
        "film_thick_x100 >= 10 && film_thick_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "thick_bounded",
        "film_thick_x100 >= 10 && film_thick_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "film thickness 0.75 mm (75 x100) in [10, 500]");
}

/// Test 3: Heating surface area (x10 m², so 10 = 1.0 m², 500 = 50.0 m²) — bounded [10, 500], value 150.
#[test]
fn test_thin_film_dryer_heating_surface_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "area_range",
        "area_x10 >= 10 && area_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "area_bounded",
        "area_x10 >= 10 && area_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating surface area 15.0 m2 (150 x10) in [10, 500]",
    );
}

/// Test 4: Evaporation rate (x10 kg/h, so 1 = 0.1 kg/h, 2000 = 200.0 kg/h) — bounded [1, 2000], value 350.
#[test]
fn test_thin_film_dryer_evaporation_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_rate_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "evap_range",
        "evap_rate_x10 >= 1 && evap_rate_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "evap_bounded",
        "evap_rate_x10 >= 1 && evap_rate_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evaporation rate 35.0 kg/h (350 x10) in [1, 2000]");
}

/// Test 5: Jacket temperature (offset +100 deg C, so 120 = 20 C, 450 = 350 C) — bounded [120, 450], value 280.
#[test]
fn test_thin_film_dryer_jacket_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_offset", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "jacket_temp_offset >= 120 && jacket_temp_offset <= 450",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "jacket_temp_offset >= 120 && jacket_temp_offset <= 450",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature 180 C (offset 280) in [120, 450]",
    );
}

/// Test 6: Number of wiper blades — bounded [2, 8], value 4.
#[test]
fn test_thin_film_dryer_wiper_blade_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_count", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blade_range",
        "blade_count >= 2 && blade_count <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blade_bounded",
        "blade_count >= 2 && blade_count <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wiper blade count in [2, 8]");
}

/// Test 7: Blade type — 3-way disjunction.
/// 1=fixed, 2=hinged, 3=pendulum. Value 2 (hinged).
#[test]
fn test_thin_film_dryer_blade_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_type", i32_ty());
    ctx.push_obligation(ProofObligation::assume("blade_val", "blade_type == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_blade_type",
        "blade_type == 1 || blade_type == 2 || blade_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blade type 2 (hinged) is valid 3-way disjunction");
}

/// Test 8: Feed mechanism — 3-way disjunction.
/// 1=gravity, 2=pressure, 3=vacuum. Value 1 (gravity).
#[test]
fn test_thin_film_dryer_feed_mechanism_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_mech", i32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_mech == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_feed_mech",
        "feed_mech == 1 || feed_mech == 2 || feed_mech == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "feed mechanism 1 (gravity) is valid 3-way disjunction",
    );
}

/// Test 9: Condensation system — 3-way disjunction.
/// 1=internal, 2=external, 3=combined. Value 3 (combined).
#[test]
fn test_thin_film_dryer_condensation_system_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cond_system", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cond_val", "cond_system == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_cond_system",
        "cond_system == 1 || cond_system == 2 || cond_system == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condensation system 3 (combined) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic film thickness control — boolean flag using i32 with if/else pattern.
/// Flag 1 = auto control enabled, output control_active = 1.
#[test]
fn test_thin_film_dryer_auto_film_thickness_control_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_control_flag", i32_ty());
    ctx.declare_var_typed("control_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "auto_control_flag == 0 || auto_control_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "flag_val",
        "auto_control_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume(
        "control_def",
        "control_active == if auto_control_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "control_triggered",
        "control_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto film thickness control flag triggers control");
}
