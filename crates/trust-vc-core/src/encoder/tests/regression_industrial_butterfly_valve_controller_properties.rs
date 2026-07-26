// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Industrial butterfly valve controller property verification.
// Encodes key parameters of an industrial butterfly valve and verifies
// that they satisfy bounded, disjunctive, and boolean-flag constraints.

/// Test 1: Disc diameter (mm) — bounded [50, 1200].
#[test]
fn test_butterfly_valve_disc_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_dia", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "disc_dia >= 50 && disc_dia <= 1200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bounded",
        "disc_dia >= 50 && disc_dia <= 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disc diameter in [50, 1200] mm");
}

/// Test 2: Pressure rating (psi) — bounded [150, 2500].
#[test]
fn test_butterfly_valve_pressure_rating_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rating", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rating_range",
        "rating >= 150 && rating <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rating_bounded",
        "rating >= 150 && rating <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure rating in [150, 2500] psi");
}

/// Test 3: Torque x10 (Nm, 0.1 Nm precision) — bounded [100, 50000].
/// 100 represents 10.0 Nm, 50000 represents 5000.0 Nm.
#[test]
fn test_butterfly_valve_torque_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("torque_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "torque_range",
        "torque_x10 >= 100 && torque_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "torque_bounded",
        "torque_x10 >= 100 && torque_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "torque x10 in [100, 50000] (10.0-5000.0 Nm)");
}

/// Test 4: Flow coefficient Cv — bounded [10, 25000].
#[test]
fn test_butterfly_valve_cv_coefficient_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cv", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cv_range",
        "cv >= 10 && cv <= 25000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cv_bounded",
        "cv >= 10 && cv <= 25000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow coefficient Cv in [10, 25000]");
}

/// Test 5: Operating temperature offset +500 (deg C) — bounded [460, 900].
/// 460 represents -40 C, 900 represents 400 C.
#[test]
fn test_butterfly_valve_operating_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp >= 460 && temp <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp >= 460 && temp <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating temp offset in [460, 900] (-40 to 400 C)",
    );
}

/// Test 6: Disc material — 3-way disjunction.
/// 1=stainless steel, 2=carbon steel, 3=Hastelloy.
#[test]
fn test_butterfly_valve_disc_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_range",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "disc material is valid 3-way disjunction");
}

/// Test 7: Seat type — 3-way disjunction.
/// 1=resilient, 2=metal, 3=fire-safe.
#[test]
fn test_butterfly_valve_seat_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seat", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seat_range",
        "seat == 1 || seat == 2 || seat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "seat_valid",
        "seat == 1 || seat == 2 || seat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "seat type is valid 3-way disjunction");
}

/// Test 8: Actuation type — 3-way disjunction.
/// 1=manual, 2=pneumatic, 3=electric.
#[test]
fn test_butterfly_valve_actuation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("act", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "act_range",
        "act == 1 || act == 2 || act == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "act_valid",
        "act == 1 || act == 2 || act == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "actuation type is valid 3-way disjunction");
}

/// Test 9: Wafer style — boolean flag (0 or 1).
#[test]
fn test_butterfly_valve_wafer_style_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ws", u32_ty());
    ctx.push_obligation(ProofObligation::assume("ws_range", "ws == 0 || ws == 1"));
    ctx.push_obligation(ProofObligation::assert("ws_valid", "ws == 0 || ws == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wafer style flag is 0 or 1");
}

/// Test 10: Cycle time x10 (seconds, 0.1 s precision) — bounded [5, 600].
/// 5 represents 0.5 s, 600 represents 60.0 s.
#[test]
fn test_butterfly_valve_cycle_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ct_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_range",
        "ct_x10 >= 5 && ct_x10 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_bounded",
        "ct_x10 >= 5 && ct_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cycle time x10 in [5, 600] (0.5-60.0 s)");
}
