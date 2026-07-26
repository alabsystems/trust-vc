// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial homogenizer controller property verification.
// Encodes key parameters of an industrial homogenizer system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Pressure (bar) — homogenizing pressure bounded [50, 1500], value 400.
#[test]
fn test_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure_bar", u32_ty());
    ctx.push_obligation(ProofObligation::assume("press_val", "pressure_bar == 400"));
    ctx.push_obligation(ProofObligation::assert("press_min", "pressure_bar >= 50"));
    ctx.push_obligation(ProofObligation::assert("press_max", "pressure_bar <= 1500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure 400 bar in [50, 1500]");
}

/// Test 2: Flow rate (L/h) — product flow rate bounded [100, 50000], value 5000.
#[test]
fn test_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_lph", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_lph == 5000"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "flow_lph >= 100"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "flow_lph <= 50000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 5000 L/h in [100, 50000]");
}

/// Test 3: Homogenizer type — 3-way disjunction.
/// 1=single stage, 2=two stage, 3=ultra-high pressure. Value 2 (two stage).
#[test]
fn test_homogenizer_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("homogenizer_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "htype_val",
        "homogenizer_type == 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_homogenizer",
        "homogenizer_type == 1 || homogenizer_type == 2 || homogenizer_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "homogenizer type 2 (two stage) is valid 3-way disjunction",
    );
}

/// Test 4: Valve design — 3-way disjunction.
/// 1=flat valve, 2=knife-edge, 3=microfluidizer. Value 1 (flat valve).
#[test]
fn test_valve_design_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve_design", u32_ty());
    ctx.push_obligation(ProofObligation::assume("valve_val", "valve_design == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_valve",
        "valve_design == 1 || valve_design == 2 || valve_design == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "valve design 1 (flat valve) is valid 3-way disjunction",
    );
}

/// Test 5: Motor power (kW) — drive motor rated power bounded [5, 500], value 55.
#[test]
fn test_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("motor_kw", u32_ty());
    ctx.push_obligation(ProofObligation::assume("pwr_val", "motor_kw == 55"));
    ctx.push_obligation(ProofObligation::assert("pwr_min", "motor_kw >= 5"));
    ctx.push_obligation(ProofObligation::assert("pwr_max", "motor_kw <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power 55 kW in [5, 500]");
}

/// Test 6: Product temperature (deg C) — all positive, bounded [5, 150], value 70.
#[test]
fn test_product_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("product_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("temp_val", "product_temp == 70"));
    ctx.push_obligation(ProofObligation::assert("temp_min", "product_temp >= 5"));
    ctx.push_obligation(ProofObligation::assert("temp_max", "product_temp <= 150"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "product temp 70 C in [5, 150]");
}

/// Test 7: Plunger count — number of plungers bounded [1, 8], value 5.
#[test]
fn test_plunger_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plunger_count", u32_ty());
    ctx.push_obligation(ProofObligation::assume("plunger_val", "plunger_count == 5"));
    ctx.push_obligation(ProofObligation::assert("plunger_min", "plunger_count >= 1"));
    ctx.push_obligation(ProofObligation::assert("plunger_max", "plunger_count <= 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "plunger count 5 in [1, 8]");
}

/// Test 8: Particle size target (x10 micrometers) — bounded [1, 500], value 10 (1.0 um).
#[test]
fn test_particle_size_target_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("size_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("size_val", "size_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert("size_min", "size_x10 >= 1"));
    ctx.push_obligation(ProofObligation::assert("size_max", "size_x10 <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "particle size 1.0 um (10 x10) in [1, 500]");
}

/// Test 9: Material — 3-way disjunction.
/// 1=SS316, 2=tungsten carbide, 3=ceramic. Value 1 (SS316).
#[test]
fn test_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "material 1 (SS316) is valid 3-way disjunction");
}

/// Test 10: Aseptic design — boolean flag using i32 with if/else pattern.
/// Flag 1 = aseptic design enabled, assert aseptic_active == 1.
#[test]
fn test_aseptic_design_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("aseptic_flag", i32_ty());
    ctx.declare_var_typed("aseptic_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "aseptic_flag == 0 || aseptic_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "aseptic_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "aseptic_def",
        "aseptic_active == if aseptic_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "aseptic_enabled",
        "aseptic_active == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "aseptic design flag enables aseptic mode");
}
