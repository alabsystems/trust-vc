// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_decanter_bowl_diameter_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dia", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bowl_diameter_range",
        "dia >= 150 && dia <= 1200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bowl_diameter_bounded",
        "dia >= 150 && dia <= 1200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl diameter 150-1200mm");
}

#[test]
fn test_decanter_bowl_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bowl_speed_range",
        "rpm >= 1000 && rpm <= 6000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bowl_speed_bounded",
        "rpm >= 1000 && rpm <= 6000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "bowl speed 1000-6000 RPM");
}

#[test]
fn test_decanter_differential_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("diff_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "differential_speed_range",
        "diff_x10 >= 5 && diff_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "differential_speed_bounded",
        "diff_x10 >= 5 && diff_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "differential speed x10 RPM 5-500");
}

#[test]
fn test_decanter_g_force_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gf", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "g_force_range",
        "gf >= 500 && gf <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "g_force_bounded",
        "gf >= 500 && gf <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "g-force 500-10000 G");
}

#[test]
fn test_decanter_feed_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("feed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "feed_rate_range",
        "feed >= 100 && feed <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "feed_rate_bounded",
        "feed >= 100 && feed <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "feed rate 100-100000 L/h");
}

#[test]
fn test_decanter_pond_depth_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pond_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pond_depth_range",
        "pond_x10 >= 50 && pond_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pond_depth_bounded",
        "pond_x10 >= 50 && pond_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pond depth x10 mm 50-500");
}

#[test]
fn test_decanter_conveyor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conveyor_type_enum",
        "conv == 1 || conv == 2 || conv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conveyor_type_valid",
        "conv == 1 || conv == 2 || conv == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "conveyor type scroll/screen/hybrid");
}

#[test]
fn test_decanter_discharge_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dis", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_type_enum",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_type_valid",
        "dis == 1 || dis == 2 || dis == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge gravity/centripetal/pressurized");
}

#[test]
fn test_decanter_wear_protection_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wear_protection_enum",
        "wp == 1 || wp == 2 || wp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wear_protection_valid",
        "wp == 1 || wp == 2 || wp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "wear protection tungsten-carbide/ceramic/stellite");
}

#[test]
fn test_decanter_explosion_proof_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ex", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "explosion_proof_bool",
        "ex == 0 || ex == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "explosion_proof_valid",
        "ex == 0 || ex == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "explosion-proof flag boolean 0 or 1");
}
