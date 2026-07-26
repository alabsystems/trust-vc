// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial contact dryer property verification.
// Encodes key parameters of an indirect contact dryer (heat transfers through
// a heated surface to the product) and verifies bounded, disjunctive, and
// boolean-flag constraints.

/// Test 1: Heating surface area (x10 m²) — scaled area bounded [10, 5000].
/// 100 represents 10.0 m² heating surface. Value 100 (10.0 m²).
#[test]
fn test_contact_dryer_heating_surface_area_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("area_val", "area_x10 == 100"));
    ctx.push_obligation(ProofObligation::assert("area_min", "area_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("area_max", "area_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating surface area 10.0 m2 (100 x10) in [10, 5000]",
    );
}

/// Test 2: Shell pressure (x10 bar) — scaled pressure bounded [1, 100].
/// 30 represents 3.0 bar. Value 30 (3.0 bar).
#[test]
fn test_contact_dryer_shell_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pres_val", "pressure_x10 == 30"));
    ctx.push_obligation(ProofObligation::assert("pres_min", "pressure_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("pres_max", "pressure_x10 <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shell pressure 3.0 bar (30 x10) in [1, 100]");
}

/// Test 3: Jacket temperature (offset +100 deg C) — bounded [100, 500].
/// 150 deg C is represented as 250. Value 250 (150 deg C).
#[test]
fn test_contact_dryer_jacket_temperature_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("jacket_temp_off", u32_ty());
    ctx.push_obligation(ProofObligation::assume("jt_val", "jacket_temp_off == 250"));
    ctx.push_obligation(ProofObligation::assert("jt_min", "jacket_temp_off >= 100"));
    ctx.push_obligation(ProofObligation::assert("jt_max", "jacket_temp_off <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "jacket temperature 150 C (offset 250) in [100, 500]",
    );
}

/// Test 4: Rotation speed (RPM) — bounded [1, 100]. Value 10 RPM.
#[test]
fn test_contact_dryer_rotation_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_rpm", u32_ty());
    ctx.push_obligation(ProofObligation::assume("spd_val", "speed_rpm == 10"));
    ctx.push_obligation(ProofObligation::assert("spd_min", "speed_rpm >= 1"));
    ctx.push_obligation(ProofObligation::assert("spd_max", "speed_rpm <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed 10 RPM in [1, 100]");
}

/// Test 5: Throughput (x10 kg/h) — scaled throughput bounded [1, 50000].
/// 500 represents 50.0 kg/h. Value 500 (50.0 kg/h).
#[test]
fn test_contact_dryer_throughput_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("throughput_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("tp_val", "throughput_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("tp_min", "throughput_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("tp_max", "throughput_x10 <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "throughput 50.0 kg/h (500 x10) in [1, 50000]");
}

/// Test 6: Number of paddles — bounded [2, 100]. Value 24 paddles.
#[test]
fn test_contact_dryer_paddle_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("paddle_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pc_val", "paddle_count == 24"));
    ctx.push_obligation(ProofObligation::assert("pc_min", "paddle_count >= 2"));
    ctx.push_obligation(ProofObligation::assert("pc_max", "paddle_count <= 100"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "paddle count 24 in [2, 100]");
}

/// Test 7: Dryer configuration — 3-way disjunction.
/// 1=disc, 2=paddle, 3=thin-film. Value 2 (paddle).
#[test]
fn test_contact_dryer_configuration_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dryer_config", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dc_val", "dryer_config == 2"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_config",
        "dryer_config == 1 || dryer_config == 2 || dryer_config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dryer configuration 2 (paddle) is valid 3-way disjunction",
    );
}

/// Test 8: Heating medium — 3-way disjunction.
/// 1=steam, 2=thermal-oil, 3=hot-water. Value 1 (steam).
#[test]
fn test_contact_dryer_heating_medium_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("heat_medium", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hm_val", "heat_medium == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_medium",
        "heat_medium == 1 || heat_medium == 2 || heat_medium == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heating medium 1 (steam) is valid 3-way disjunction",
    );
}

/// Test 9: Discharge type — 3-way disjunction.
/// 1=overflow-weir, 2=bottom-valve, 3=screw-conveyor. Value 3 (screw-conveyor).
#[test]
fn test_contact_dryer_discharge_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("discharge_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("dt_val", "discharge_type == 3"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_discharge",
        "discharge_type == 1 || discharge_type == 2 || discharge_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge type 3 (screw-conveyor) is valid 3-way disjunction",
    );
}

/// Test 10: Automatic vacuum control — boolean flag using i32 with if/else.
/// Flag 1 = vacuum control enabled, which activates vacuum regulation (vacuum_active = 1).
#[test]
fn test_contact_dryer_vacuum_control_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum_flag", i32_ty());
    ctx.declare_var_typed("vacuum_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "vacuum_flag == 0 || vacuum_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "vacuum_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "vacuum_def",
        "vacuum_active == if vacuum_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("vacuum_on", "vacuum_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum control flag activates vacuum regulation");
}
