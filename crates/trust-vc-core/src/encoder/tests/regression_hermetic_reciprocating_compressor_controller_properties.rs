// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_hermetic_recip_suction_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("suct_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suct_range",
        "suct_x10 >= 10 && suct_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suct_bounded",
        "suct_x10 >= 10 && suct_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suction pressure x10 bar must be in range 10-500 representing 1.0-50.0 bar",
    );
}

#[test]
fn test_hermetic_recip_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disc_range",
        "disc_x10 >= 50 && disc_x10 <= 3500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disc_bounded",
        "disc_x10 >= 50 && disc_x10 <= 3500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 bar must be in range 50-3500 representing 5.0-350.0 bar",
    );
}

#[test]
fn test_hermetic_recip_motor_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_range",
        "curr_x100 >= 10 && curr_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curr_bounded",
        "curr_x100 >= 10 && curr_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "motor current x100 A must be in range 10-50000 representing 0.10-500.00 A",
    );
}

#[test]
fn test_hermetic_recip_winding_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wtemp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wtemp_range",
        "wtemp_off >= 150 && wtemp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wtemp_bounded",
        "wtemp_off >= 150 && wtemp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "winding temp offset +100 C must be in range 150-350 representing 50-250 C",
    );
}

#[test]
fn test_hermetic_recip_displacement_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "disp_x100 >= 10 && disp_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disp_bounded",
        "disp_x100 >= 10 && disp_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "displacement x100 cm3/rev must be in range 10-50000 representing 0.10-500.00 cm3/rev",
    );
}

#[test]
fn test_hermetic_recip_oil_level_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_range",
        "oil_x100 >= 0 && oil_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_bounded",
        "oil_x100 >= 0 && oil_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil level x100 pct must be in range 0-10000 representing 0.00-100.00 pct",
    );
}

#[test]
fn test_hermetic_recip_refrigerant_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrigerant", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "refrig_range",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "refrig_valid",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refrigerant type must be R134a (1), R410A (2), or R290 (3)",
    );
}

#[test]
fn test_hermetic_recip_capacity_step_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("step", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "step_range",
        "step == 1 || step == 2 || step == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "step_valid",
        "step == 1 || step == 2 || step == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity step must be full (1), half (2), or quarter (3)",
    );
}

#[test]
fn test_hermetic_recip_protection_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("protect", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "protect_range",
        "protect == 1 || protect == 2 || protect == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "protect_valid",
        "protect == 1 || protect == 2 || protect == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protection mode must be thermal (1), current (2), or pressure (3)",
    );
}

#[test]
fn test_hermetic_recip_auto_restart_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto restart flag must be 0 (disabled) or 1 (enabled)",
    );
}
