// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

/// Test 1: Piston stroke (x100 mm) — bounded [100, 10000].
/// 100 represents 1.00 mm, 5000 represents 50.00 mm.
#[test]
fn test_free_piston_stroke_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stroke_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stk_a",
        "stroke_x100 >= 100 && stroke_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stk_c",
        "stroke_x100 >= 100 && stroke_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "piston stroke x100 in [100, 10000] representing 1.00-100.00 mm",
    );
}

/// Test 2: Operating frequency (x10 Hz) — bounded [100, 2000].
/// 100 represents 10.0 Hz, 2000 represents 200.0 Hz.
#[test]
fn test_free_piston_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_a",
        "freq_x10 >= 100 && freq_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_c",
        "freq_x10 >= 100 && freq_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "operating frequency x10 in [100, 2000] representing 10.0-200.0 Hz",
    );
}

/// Test 3: Discharge pressure (x10 bar) — bounded [10, 5000].
/// 10 represents 1.0 bar, 5000 represents 500.0 bar.
#[test]
fn test_free_piston_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "disc_x10 >= 10 && disc_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "disc_x10 >= 10 && disc_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 in [10, 5000] representing 1.0-500.0 bar",
    );
}

/// Test 4: Spring stiffness (N/m) — bounded [1000, 500000].
#[test]
fn test_free_piston_spring_stiffness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("stiffness", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "stiff_a",
        "stiffness >= 1000 && stiffness <= 500000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "stiff_c",
        "stiffness >= 1000 && stiffness <= 500000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "spring stiffness in [1000, 500000] N/m");
}

/// Test 5: Motor current (x100 A) — bounded [10, 30000].
/// 10 represents 0.10 A, 30000 represents 300.00 A.
#[test]
fn test_free_piston_motor_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_a",
        "curr_x100 >= 10 && curr_x100 <= 30000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curr_c",
        "curr_x100 >= 10 && curr_x100 <= 30000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor current x100 in [10, 30000] representing 0.10-300.00 A",
    );
}

/// Test 6: Piston position sensor reading (x1000 mm) — bounded [0, 100000].
/// 0 represents 0.000 mm, 100000 represents 100.000 mm.
#[test]
fn test_free_piston_position_sensor_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pos_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pos_a",
        "pos_x1000 >= 0 && pos_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pos_c",
        "pos_x1000 >= 0 && pos_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "position sensor x1000 in [0, 100000] representing 0.000-100.000 mm",
    );
}

/// Test 7: Drive type — 3-way disjunction.
/// 1=linear-motor, 2=gas-spring, 3=flexure-bearing.
#[test]
fn test_free_piston_drive_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drive", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drive_a",
        "drive == 1 || drive == 2 || drive == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drive_c",
        "drive >= 1 && drive <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drive type 3-way (linear-motor/gas-spring/flexure-bearing)",
    );
}

/// Test 8: Control strategy — 3-way disjunction.
/// 1=open-loop, 2=stroke-control, 3=resonance-tracking.
#[test]
fn test_free_piston_control_strategy_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_a",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert("ctrl_c", "ctrl >= 1 && ctrl <= 3"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "control strategy 3-way (open-loop/stroke-control/resonance-tracking)",
    );
}

/// Test 9: Working fluid — 3-way disjunction.
/// 1=helium, 2=nitrogen, 3=refrigerant.
#[test]
fn test_free_piston_working_fluid_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fluid", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fluid_a",
        "fluid == 1 || fluid == 2 || fluid == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fluid_c",
        "fluid >= 1 && fluid <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "working fluid 3-way (helium/nitrogen/refrigerant)");
}

/// Test 10: Over-stroke protection flag — boolean.
/// 0=disabled, 1=enabled.
#[test]
fn test_free_piston_overstroke_protection_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("flag_c", "flag >= 0 && flag <= 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "over-stroke protection flag is boolean (0 or 1)");
}
