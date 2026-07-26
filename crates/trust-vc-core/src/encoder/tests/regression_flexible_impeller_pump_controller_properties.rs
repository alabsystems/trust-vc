//! Flexible impeller pump controller property regression tests.
//!
//! These tests model key bounded parameters of flexible impeller pump
//! controllers: flow rate, pressure, speed, impeller diameter, blade count,
//! suction lift, impeller material, housing material, drive type, and
//! run-dry capability. Each test assumes a bounded range, then asserts
//! the same constraint holds.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// Flow rate scaled by 10 (0.1 L/min resolution): 1..=5000.
#[test]
fn test_flex_imp_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_lower",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 1 && flow_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 should stay in [1, 5000]");
}

/// Pressure scaled by 10 (0.1 bar resolution): 5..=40.
#[test]
fn test_flex_imp_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 5 && press_x10 <= 40",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 5 && press_x10 <= 40",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure x10 should stay in [5, 40]");
}

/// Rotor speed: 100..=2000 RPM.
#[test]
fn test_flex_imp_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rpm_range",
        "rpm >= 100 && rpm <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rpm_bounded",
        "rpm >= 100 && rpm <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed should stay in [100, 2000] RPM");
}

/// Impeller diameter: 30..=200 mm.
#[test]
fn test_flex_imp_impeller_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dia_range",
        "dia >= 30 && dia <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dia_bounded",
        "dia >= 30 && dia <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "impeller diameter should stay in [30, 200] mm");
}

/// Blade count: 6..=12.
#[test]
fn test_flex_imp_blade_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("blades", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "blades_range",
        "blades >= 6 && blades <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "blades_bounded",
        "blades >= 6 && blades <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "blade count should stay in [6, 12]");
}

/// Suction lift scaled by 10 (0.1 m resolution): 10..=60.
#[test]
fn test_flex_imp_suction_lift_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("lift_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lift_range",
        "lift_x10 >= 10 && lift_x10 <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lift_bounded",
        "lift_x10 >= 10 && lift_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "suction lift x10 should stay in [10, 60]");
}

/// Impeller material: 1=neoprene, 2=nitrile, 3=EPDM.
#[test]
fn test_flex_imp_impeller_material_three_way() {
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
    expect_verified(&result, "impeller material should be one of {1, 2, 3}");
}

/// Housing material: 1=bronze, 2=stainless, 3=polypropylene.
#[test]
fn test_flex_imp_housing_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hsg", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hsg_valid",
        "hsg == 1 || hsg == 2 || hsg == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hsg_enum",
        "hsg == 1 || hsg == 2 || hsg == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "housing material should be one of {1, 2, 3}");
}

/// Drive type: 1=direct, 2=belt, 3=clutch.
#[test]
fn test_flex_imp_drive_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drv_valid",
        "drv == 1 || drv == 2 || drv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drv_enum",
        "drv == 1 || drv == 2 || drv == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive type should be one of {1, 2, 3}");
}

/// Run-dry capable flag: boolean encoded as 0 or 1.
#[test]
fn test_flex_imp_run_dry_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rd", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rd_valid", "rd == 0 || rd == 1"));
    ctx.push_obligation(ProofObligation::assert("rd_bool", "rd == 0 || rd == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "run-dry flag should be 0 or 1");
}
