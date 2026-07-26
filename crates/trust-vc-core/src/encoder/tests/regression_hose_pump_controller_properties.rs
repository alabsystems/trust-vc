//! Hose pump controller property regression tests.
//!
//! These tests model key bounded parameters of industrial hose (peristaltic)
//! pump controllers: flow rate, pressure, speed, bore, suction lift, solids
//! passage, hose material, shoe count, lubrication mode, and reversibility.
//! Each test assumes a bounded range, then asserts the same constraint holds.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// Flow rate scaled by 10 (0.1 L/min resolution): 1..=50000.
#[test]
fn test_hose_pump_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_lower",
        "flow_x10 >= 1 && flow_x10 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 should stay in [1, 50000]");
}

/// Operating pressure: 1..=16 bar.
#[test]
fn test_hose_pump_pressure_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press >= 1 && press <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press >= 1 && press <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure should stay in [1, 16] bar");
}

/// Rotor speed: 5..=80 RPM.
#[test]
fn test_hose_pump_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 5 && rpm <= 80",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 5 && rpm <= 80",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed should stay in [5, 80] RPM");
}

/// Hose bore diameter: 10..=150 mm.
#[test]
fn test_hose_pump_hose_bore_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bore", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bore_range",
        "bore >= 10 && bore <= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bore_bounded",
        "bore >= 10 && bore <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hose bore should stay in [10, 150] mm");
}

/// Suction lift: 1..=10 m.
#[test]
fn test_hose_pump_suction_lift_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lift", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lift_range",
        "lift >= 1 && lift <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lift_bounded",
        "lift >= 1 && lift <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "suction lift should stay in [1, 10] m");
}

/// Solids passage diameter: 1..=100 mm.
#[test]
fn test_hose_pump_solids_passage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sol", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sol_range",
        "sol >= 1 && sol <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sol_bounded",
        "sol >= 1 && sol <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "solids passage should stay in [1, 100] mm");
}

/// Hose material: 1=natural rubber, 2=EPDM, 3=nitrile.
#[test]
fn test_hose_pump_hose_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_valid",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_enum",
        "mat == 1 || mat == 2 || mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "hose material should be one of {1, 2, 3}");
}

/// Shoe count: 1=two-shoe, 2=three-shoe, 3=roller.
#[test]
fn test_hose_pump_shoe_count_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("shoe", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "shoe_valid",
        "shoe == 1 || shoe == 2 || shoe == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "shoe_enum",
        "shoe == 1 || shoe == 2 || shoe == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "shoe count should be one of {1, 2, 3}");
}

/// Lubrication mode: 1=glycol, 2=oil, 3=dry-running.
#[test]
fn test_hose_pump_lubrication_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lub", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lub_valid",
        "lub == 1 || lub == 2 || lub == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lub_enum",
        "lub == 1 || lub == 2 || lub == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "lubrication mode should be one of {1, 2, 3}");
}

/// Reversible flag: boolean encoded as 0 or 1.
#[test]
fn test_hose_pump_reversible_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rev", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rev_valid", "rev == 0 || rev == 1"));
    ctx.push_obligation(ProofObligation::assert("rev_bool", "rev == 0 || rev == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reversible flag should be 0 or 1");
}
