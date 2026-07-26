// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial agitated thin film dryer (ATFD / wiped film evaporator) property verification.
// Encodes key parameters of an ATFD system and verifies that they satisfy bounded,
// disjunctive, and boolean-flag constraints.

/// Test 1: Evaporation area (x10 m², so 50 = 5.0 m²) — bounded [1, 500], value 50.
#[test]
fn test_atfd_evaporation_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("evap_area_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("area_val", "evap_area_x10 == 50"));
    ctx.push_obligation(ProofObligation::assert("area_min", "evap_area_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("area_max", "evap_area_x10 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "evaporation area 5.0 m2 (50 x10) in [1, 500]");
}

/// Test 2: Rotor speed (RPM) — bounded [50, 2000], value 500.
#[test]
fn test_atfd_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rotor_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("rpm_val", "rotor_rpm == 500"));
    ctx.push_obligation(ProofObligation::assert("rpm_min", "rotor_rpm >= 50"));
    ctx.push_obligation(ProofObligation::assert("rpm_max", "rotor_rpm <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed 500 RPM in [50, 2000]");
}

/// Test 3: Jacket temperature (offset +100 deg C, so 300 = 200 deg C) — bounded [100, 600], value 300.
#[test]
fn test_atfd_jacket_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_offset", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_val",
        "jacket_temp_offset == 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_min",
        "jacket_temp_offset >= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_max",
        "jacket_temp_offset <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature 200 C (offset 300) in [100, 600]",
    );
}

/// Test 4: Film thickness (x100 mm, so 10 = 0.10 mm) — bounded [1, 500], value 10.
#[test]
fn test_atfd_film_thickness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("film_thick_x100", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "thick_val",
        "film_thick_x100 == 10",
    ));
    ctx.push_obligation(ProofObligation::assert("thick_min", "film_thick_x100 >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "thick_max",
        "film_thick_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "film thickness 0.10 mm (10 x100) in [1, 500]");
}

/// Test 5: Feed rate (x10 L/h, so 500 = 50.0 L/h) — bounded [1, 50000], value 500.
#[test]
fn test_atfd_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed_rate_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("feed_val", "feed_rate_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("feed_min", "feed_rate_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert(
        "feed_max",
        "feed_rate_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 50.0 L/h (500 x10) in [1, 50000]");
}

/// Test 6: Number of wiper blades — bounded [2, 12], value 4.
#[test]
fn test_atfd_wiper_blade_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blade_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("blade_val", "blade_count == 4"));
    ctx.push_obligation(ProofObligation::assert("blade_min", "blade_count >= 2"));
    ctx.push_obligation(ProofObligation::assert("blade_max", "blade_count <= 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wiper blade count 4 in [2, 12]");
}

/// Test 7: Wiper type — 3-way disjunction.
/// 1=hinged, 2=fixed, 3=rolling. Value 1 (hinged).
#[test]
fn test_atfd_wiper_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wiper_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("wiper_val", "wiper_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_wiper",
        "wiper_type == 1 || wiper_type == 2 || wiper_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wiper type 1 (hinged) is valid 3-way disjunction");
}

/// Test 8: Heating method — 3-way disjunction.
/// 1=steam-jacket, 2=thermal-oil, 3=electric. Value 2 (thermal-oil).
#[test]
fn test_atfd_heating_method_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heating_method", u32_ty());
    ctx.push_obligation(ProofObligation::assume("heat_val", "heating_method == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_heating",
        "heating_method == 1 || heating_method == 2 || heating_method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating method 2 (thermal-oil) is valid 3-way disjunction",
    );
}

/// Test 9: Condensation type — 3-way disjunction.
/// 1=internal, 2=external, 3=short-path. Value 3 (short-path).
#[test]
fn test_atfd_condensation_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("condensation_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cond_val",
        "condensation_type == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_condensation",
        "condensation_type == 1 || condensation_type == 2 || condensation_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "condensation type 3 (short-path) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic viscosity compensation — boolean flag using i32 with if/else pattern.
/// Flag 1 = viscosity compensation enabled, output compensation_active = 1.
#[test]
fn test_atfd_viscosity_compensation_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("visc_comp_flag", i32_ty());
    ctx.declare_var_typed("compensation_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "visc_comp_flag == 0 || visc_comp_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "visc_comp_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "comp_def",
        "compensation_active == if visc_comp_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "comp_triggered",
        "compensation_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "viscosity compensation flag triggers compensation");
}
