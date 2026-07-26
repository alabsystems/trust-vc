// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Industrial plate heat exchanger property verification.
// Encodes key parameters of a plate heat exchanger system and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Plate count — bounded [5, 500], value 50.
#[test]
fn test_plate_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plates", u32_ty());
    ctx.push_obligation(ProofObligation::assume("plates_val", "plates == 50"));
    ctx.push_obligation(ProofObligation::assert("plates_min", "plates >= 5"));
    ctx.push_obligation(ProofObligation::assert("plates_max", "plates <= 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "plate count 50 in [5, 500]");
}

/// Test 2: Heat transfer area (x10 m^2) — bounded [10, 5000], value 300 (30.0 m^2).
#[test]
fn test_heat_transfer_area_scaled_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("area_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume("area_val", "area_x10 == 300"));
    ctx.push_obligation(ProofObligation::assert("area_min", "area_x10 >= 10"));
    ctx.push_obligation(ProofObligation::assert("area_max", "area_x10 <= 5000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "heat transfer area 30.0 m^2 (300 x10) in [10, 5000]",
    );
}

/// Test 3: Design pressure (bar) — bounded [5, 40], value 25.
#[test]
fn test_design_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", u32_ty());
    ctx.push_obligation(ProofObligation::assume("press_val", "pressure == 25"));
    ctx.push_obligation(ProofObligation::assert("press_min", "pressure >= 5"));
    ctx.push_obligation(ProofObligation::assert("press_max", "pressure <= 40"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "design pressure 25 bar in [5, 40]");
}

/// Test 4: Plate type — 3-way disjunction.
/// 1=gasketed, 2=welded, 3=brazed. Value 1 (gasketed).
#[test]
fn test_plate_type_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plate_type", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ptype_val", "plate_type == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_plate_type",
        "plate_type == 1 || plate_type == 2 || plate_type == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plate type 1 (gasketed) is valid 3-way disjunction",
    );
}

/// Test 5: Flow arrangement — 3-way disjunction.
/// 1=parallel, 2=counter-current, 3=mixed. Value 2 (counter-current).
#[test]
fn test_flow_arrangement_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_arrangement", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_arr_val",
        "flow_arrangement == 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_flow_arrangement",
        "flow_arrangement == 1 || flow_arrangement == 2 || flow_arrangement == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow arrangement 2 (counter-current) is valid 3-way disjunction",
    );
}

/// Test 6: Plate material — 3-way disjunction.
/// 1=SS316, 2=titanium, 3=Hastelloy. Value 1 (SS316).
#[test]
fn test_plate_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("plate_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume("mat_val", "plate_material == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "valid_material",
        "plate_material == 1 || plate_material == 2 || plate_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plate material 1 (SS316) is valid 3-way disjunction",
    );
}

/// Test 7: Hot side temperature (deg C) — bounded [30, 200], value 90.
#[test]
fn test_hot_side_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hot_temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume("hot_val", "hot_temp == 90"));
    ctx.push_obligation(ProofObligation::assert("hot_min", "hot_temp >= 30"));
    ctx.push_obligation(ProofObligation::assert("hot_max", "hot_temp <= 200"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hot side temp 90 C in [30, 200]");
}

/// Test 8: Flow rate (m^3/h) — bounded [1, 1000], value 100.
#[test]
fn test_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow", u32_ty());
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow == 100"));
    ctx.push_obligation(ProofObligation::assert("flow_min", "flow >= 1"));
    ctx.push_obligation(ProofObligation::assert("flow_max", "flow <= 1000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate 100 m^3/h in [1, 1000]");
}

/// Test 9: Gasket material — 3-way disjunction.
/// 1=NBR, 2=EPDM, 3=Viton. Value 2 (EPDM).
#[test]
fn test_gasket_material_three_way_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gasket_material", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gasket_val",
        "gasket_material == 2",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valid_gasket",
        "gasket_material == 1 || gasket_material == 2 || gasket_material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "gasket material 2 (EPDM) is valid 3-way disjunction",
    );
}

/// Test 10: CIP connection — boolean flag using i32 with if/else pattern.
/// Flag 1 = CIP connection present.
#[test]
fn test_cip_connection_boolean_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cip_flag", i32_ty());
    ctx.declare_var_typed("cip_active", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_domain",
        "cip_flag == 0 || cip_flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assume("flag_val", "cip_flag == 1"));
    ctx.push_obligation(ProofObligation::assume(
        "cip_def",
        "cip_active == if cip_flag == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("cip_present", "cip_active == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CIP connection flag triggers active");
}
