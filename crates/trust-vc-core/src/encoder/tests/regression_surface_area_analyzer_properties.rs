// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_bet_surface_area_min_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sa_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sa_x100 >= 1 && sa_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sa_x100 >= 1 && sa_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "min surface area x100 in [1, 100] should stay bounded",
    );
}

#[test]
fn test_bet_surface_area_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sa_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sa_max >= 1 && sa_max <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "sa_max >= 1 && sa_max <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max surface area in [1, 5000] m2/g should stay bounded",
    );
}

#[test]
fn test_bet_pore_size_min_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pore_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pore_x10 >= 1 && pore_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pore_x10 >= 1 && pore_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min pore size x10 in [1, 100] should stay bounded");
}

#[test]
fn test_bet_pore_size_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pore_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pore_max >= 100 && pore_max <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "pore_max >= 100 && pore_max <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "max pore size in [100, 5000] nm should stay bounded",
    );
}

#[test]
fn test_bet_sample_stations_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("st", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "st >= 1 && st <= 12"));
    ctx.push_obligation(ProofObligation::assert("bounded", "st >= 1 && st <= 12"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample stations in [1, 12] should stay bounded");
}

#[test]
fn test_bet_degas_temp_offset500_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "temp >= 550 && temp <= 900",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "temp >= 550 && temp <= 900",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "degas temp offset+500 in [550, 900] should stay bounded",
    );
}

#[test]
fn test_bet_adsorbate_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("gas", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "gas == 1 || gas == 2 || gas == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "adsorbate should be nitrogen, krypton, or argon");
}

#[test]
fn test_bet_analysis_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "analysis method should be multipoint, single-point, or volumetric",
    );
}

#[test]
fn test_bet_pore_distribution_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dist", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid",
        "dist == 1 || dist == 2 || dist == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "dist == 1 || dist == 2 || dist == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pore distribution should be BJH, DFT, or HK");
}

#[test]
fn test_bet_cryogen_free_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cf", i32_ty());
    ctx.push_obligation(ProofObligation::assume("valid", "cf == 0 || cf == 1"));
    ctx.push_obligation(ProofObligation::assert("bounded", "cf == 0 || cf == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cryogen-free flag should be boolean");
}
