// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_labyrinth_seal_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "press_x10 >= 10 && press_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "press_x10 >= 10 && press_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "labyrinth seal discharge pressure x10 bounded");
}

#[test]
fn test_labyrinth_seal_piston_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ps_a",
        "speed >= 200 && speed <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ps_c",
        "speed >= 200 && speed <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "labyrinth seal piston speed bounded");
}

#[test]
fn test_labyrinth_seal_cylinder_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cyl_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ct_a",
        "cyl_temp >= 130 && cyl_temp <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ct_c",
        "cyl_temp >= 130 && cyl_temp <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "labyrinth seal cylinder temperature offset+100 bounded",
    );
}

#[test]
fn test_labyrinth_seal_clearance_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("clr_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cl_a",
        "clr_x1000 >= 10 && clr_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cl_c",
        "clr_x1000 >= 10 && clr_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "labyrinth seal clearance x1000 bounded");
}

#[test]
fn test_labyrinth_seal_leakage_rate_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "lr_a",
        "leak_x100 >= 1 && leak_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "lr_c",
        "leak_x100 >= 1 && leak_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "labyrinth seal leakage rate x100 bounded");
}

#[test]
fn test_labyrinth_seal_number_of_grooves_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("grooves", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ng_a",
        "grooves >= 3 && grooves <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ng_c",
        "grooves >= 3 && grooves <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "labyrinth seal number of grooves bounded");
}

#[test]
fn test_labyrinth_seal_groove_profile_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("profile", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gp_a",
        "profile == 1 || profile == 2 || profile == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gp_c",
        "profile == 1 || profile == 2 || profile == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "labyrinth seal groove profile three-way disjunction",
    );
}

#[test]
fn test_labyrinth_seal_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sm_a",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sm_c",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "labyrinth seal material three-way disjunction");
}

#[test]
fn test_labyrinth_seal_gas_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "gt_a",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "gt_c",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "labyrinth seal gas type three-way disjunction");
}

#[test]
fn test_labyrinth_seal_auto_clearance_monitor_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("cm_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("cm_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "labyrinth seal auto clearance monitor flag");
}
