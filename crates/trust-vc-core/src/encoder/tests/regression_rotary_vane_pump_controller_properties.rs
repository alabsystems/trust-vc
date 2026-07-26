// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 10 && flow_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assume("flow_val", "flow_x10 == 500"));
    ctx.push_obligation(ProofObligation::assert("flow_at_50_lpm", "flow_x10 == 500"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 at 50.0 L/min should verify");
}

#[test]
fn test_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("press_val", "press_x10 == 80"));
    ctx.push_obligation(ProofObligation::assert("press_at_8_bar", "press_x10 == 80"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pressure x10 at 8.0 bar should verify");
}

#[test]
fn test_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 100 && speed <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assume("speed_val", "speed == 1800"));
    ctx.push_obligation(ProofObligation::assert(
        "speed_at_1800_rpm",
        "speed == 1800",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "speed at 1800 RPM should verify");
}

#[test]
fn test_vane_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vanes", u8_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vane_range",
        "vanes >= 4 && vanes <= 16",
    ));
    ctx.push_obligation(ProofObligation::assume("vane_val", "vanes == 8"));
    ctx.push_obligation(ProofObligation::assert("eight_vanes", "vanes == 8"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vane count of 8 should verify");
}

#[test]
fn test_displacement_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "disp_x10 >= 10 && disp_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assume("disp_val", "disp_x10 == 1200"));
    ctx.push_obligation(ProofObligation::assert(
        "disp_at_120_cc",
        "disp_x10 == 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement x10 at 120.0 cc/rev should verify");
}

#[test]
fn test_vacuum_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vac_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vac_range",
        "vac_x10 >= 1 && vac_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assume("vac_val", "vac_x10 == 5"));
    ctx.push_obligation(ProofObligation::assert("vac_at_half_mbar", "vac_x10 == 5"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum x10 at 0.5 mbar ultimate should verify");
}

#[test]
fn test_housing_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("housing", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "housing_valid",
        "housing == 1 || housing == 2 || housing == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "housing_in_range",
        "housing >= 1 && housing <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "housing material 1=cast-iron 2=stainless 3=aluminum should verify",
    );
}

#[test]
fn test_vane_material_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vane_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vane_mat_valid",
        "vane_mat == 1 || vane_mat == 2 || vane_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vane_mat_in_range",
        "vane_mat >= 1 && vane_mat <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "vane material 1=graphite 2=PEEK 3=phenolic should verify",
    );
}

#[test]
fn test_seal_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("seal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "seal_valid",
        "seal == 1 || seal == 2 || seal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "seal_in_range",
        "seal >= 1 && seal <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "seal type 1=mechanical 2=lip 3=magnetic-coupling should verify",
    );
}

#[test]
fn test_oil_free_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oilfree", i32_ty());
    ctx.push_obligation(ProofObligation::assume("oilfree_true", "oilfree == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "flag_is_one",
        "if oilfree == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oil-free boolean flag set to 1 should verify");
}
