// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_radiant_panel_panel_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("panel_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pt_a",
        "panel_temp >= 200 && panel_temp <= 700",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pt_c",
        "panel_temp >= 200 && panel_temp <= 700",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiant panel temperature offset+100 bounded");
}

#[test]
fn test_radiant_panel_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pp_a",
        "power_x10 >= 1 && power_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pp_c",
        "power_x10 >= 1 && power_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiant panel power x10 bounded");
}

#[test]
fn test_radiant_panel_conveyor_speed_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cs_a",
        "speed_x100 >= 1 && speed_x100 <= 800",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cs_c",
        "speed_x100 >= 1 && speed_x100 <= 800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiant panel conveyor speed x100 bounded");
}

#[test]
fn test_radiant_panel_air_gap_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gap", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ag_a", "gap >= 20 && gap <= 300"));
    ctx.push_obligation(ProofObligation::assert("ag_c", "gap >= 20 && gap <= 300"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiant panel air gap bounded");
}

#[test]
fn test_radiant_panel_product_thickness_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("thickness", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "th_a",
        "thickness >= 1 && thickness <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "th_c",
        "thickness >= 1 && thickness <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiant panel product thickness bounded");
}

#[test]
fn test_radiant_panel_exposure_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exposure", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "et_a",
        "exposure >= 1 && exposure <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "et_c",
        "exposure >= 1 && exposure <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiant panel exposure time bounded");
}

#[test]
fn test_radiant_panel_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pm_a",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pm_c",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiant panel material three-way disjunction");
}

#[test]
fn test_radiant_panel_heat_distribution_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("distrib", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "hd_a",
        "distrib == 1 || distrib == 2 || distrib == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "hd_c",
        "distrib == 1 || distrib == 2 || distrib == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "radiant panel heat distribution three-way disjunction",
    );
}

#[test]
fn test_radiant_panel_cooling_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cooling", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_a",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_c",
        "cooling == 1 || cooling == 2 || cooling == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "radiant panel cooling method three-way disjunction",
    );
}

#[test]
fn test_radiant_panel_auto_temp_compensation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("tc_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "radiant panel auto temperature compensation flag");
}
