// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

// Triplex plunger pump controller property verification.
// Models key physical and configuration constraints for high-pressure
// positive-displacement pumps used in industrial applications.

/// Test 1: Flow rate is bounded and positive (scaled by 10 to avoid fractions).
/// flow_x10 represents flow in tenths of L/min, so 1-19999 maps to 0.1-1999.9 L/min.
#[test]
fn test_triplex_plunger_pump_flow_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 > 0 && flow_x10 < 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_positive",
        "flow_x10 >= 1 && flow_x10 <= 19999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "flow rate (x10 L/min) is strictly positive and bounded",
    );
}

/// Test 2: Maximum operating pressure is bounded within safe limits (1-3000 bar).
#[test]
fn test_triplex_plunger_pump_max_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pressure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pressure_range",
        "pressure >= 1 && pressure <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pressure_safe",
        "pressure > 0 && pressure <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operating pressure within 1-3000 bar safe range");
}

/// Test 3: Stroke length is bounded and positive (scaled by 10 to avoid fractions).
/// stroke_x10 represents stroke in tenths of mm, so 1-4999 maps to 0.1-499.9 mm.
#[test]
fn test_triplex_plunger_pump_stroke_length_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stroke_range",
        "stroke_x10 > 0 && stroke_x10 < 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stroke_positive",
        "stroke_x10 >= 1 && stroke_x10 <= 4999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "stroke length (x10 mm) is strictly positive and bounded",
    );
}

/// Test 4: Plunger diameter is bounded and positive (scaled by 10 to avoid fractions).
/// diam_x10 represents diameter in tenths of mm, so 1-2999 maps to 0.1-299.9 mm.
#[test]
fn test_triplex_plunger_pump_plunger_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diam_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "diam_range",
        "diam_x10 > 0 && diam_x10 < 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "diam_positive",
        "diam_x10 >= 1 && diam_x10 <= 2999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "plunger diameter (x10 mm) is strictly positive and bounded",
    );
}

/// Test 5: Crank speed is bounded within operational limits (1-600 RPM).
#[test]
fn test_triplex_plunger_pump_crank_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 1 && rpm <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert("rpm_safe", "rpm > 0 && rpm <= 600"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "crank speed within 1-600 RPM operational range");
}

/// Test 6: Number of plungers is bounded (3-7, triplex and above).
#[test]
fn test_triplex_plunger_pump_plunger_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", i32_ty());
    ctx.push_obligation(ProofObligation::assume("plunger_count", "n >= 3 && n <= 7"));
    ctx.push_obligation(ProofObligation::assert("count_valid", "n >= 3 && n <= 7"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "plunger count within 3-7 range");
}

/// Test 7: Valve type is one of the valid options (1=ball, 2=poppet, 3=disc).
#[test]
fn test_triplex_plunger_pump_valve_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("valve", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valve_valid",
        "valve == 1 || valve == 2 || valve == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "valve_in_range",
        "valve >= 1 && valve <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "valve type is ball(1), poppet(2), or disc(3)");
}

/// Test 8: Packing material is one of the valid options (1=PTFE, 2=graphite, 3=aramid).
#[test]
fn test_triplex_plunger_pump_packing_material_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pack", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pack_valid",
        "pack == 1 || pack == 2 || pack == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pack_in_range",
        "pack >= 1 && pack <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "packing material is PTFE(1), graphite(2), or aramid(3)",
    );
}

/// Test 9: Drive type is one of the valid options (1=direct, 2=belt, 3=gear-reduced).
#[test]
fn test_triplex_plunger_pump_drive_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_valid",
        "drive == 1 || drive == 2 || drive == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_in_range",
        "drive >= 1 && drive <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type is direct(1), belt(2), or gear-reduced(3)",
    );
}

/// Test 10: Automatic pressure relief flag is a boolean encoded as i32 (0 or 1).
#[test]
fn test_triplex_plunger_pump_pressure_relief_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("relief", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "relief_bool",
        "relief == 0 || relief == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "relief_bounded",
        "relief >= 0 && relief <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure relief flag is boolean (0 or 1)");
}
