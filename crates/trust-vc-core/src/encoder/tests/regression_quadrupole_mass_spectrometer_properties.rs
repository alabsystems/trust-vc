// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("max_amu", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "max_amu >= 100 && max_amu <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "max_amu == 1024"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "max_amu >= 100 && max_amu <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QMS max amu 1024 within [100, 3000]");
}

#[test]
fn resolution_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "res_x10 >= 1 && res_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "res_x10 == 10"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "res_x10 >= 1 && res_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QMS resolution x10=10 (1.0 amu) within [1, 50]");
}

#[test]
fn sensitivity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("counts_per_ppm", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "counts_per_ppm >= 100 && counts_per_ppm <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "counts_per_ppm == 100000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "counts_per_ppm >= 100 && counts_per_ppm <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "QMS sensitivity 100000 counts/ppm within [100, 1000000]",
    );
}

#[test]
fn scan_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("amu_per_sec", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "amu_per_sec >= 100 && amu_per_sec <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "amu_per_sec == 10000"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "amu_per_sec >= 100 && amu_per_sec <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QMS scan speed 10000 amu/s within [100, 100000]");
}

#[test]
fn rod_diameter_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rod_dia_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rod_dia_x10 >= 50 && rod_dia_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rod_dia_x10 == 95"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rod_dia_x10 >= 50 && rod_dia_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QMS rod diameter x10=95 (9.5 mm) within [50, 200]");
}

#[test]
fn rf_frequency_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rf_freq_x10", u32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "rf_freq_x10 >= 10 && rf_freq_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assume("val", "rf_freq_x10 == 19"));
    ctx.push_obligation(ProofObligation::assert(
        "bounded",
        "rf_freq_x10 >= 10 && rf_freq_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QMS RF frequency x10=19 (1.9 MHz) within [10, 50]");
}

#[test]
fn ionization_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_mode",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid",
        "ion_mode == 1 || ion_mode == 2 || ion_mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QMS ionization mode in {EI=1, CI=2, APCI=3}");
}

#[test]
fn analyzer_mode_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_mode",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QMS analyzer mode in {scan=1, SIM=2, MRM=3}");
}

#[test]
fn vacuum_pump_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pump", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "valid_pump",
        "pump == 1 || pump == 2 || pump == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_valid",
        "pump == 1 || pump == 2 || pump == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "QMS vacuum pump in {turbo=1, diffusion=2, ion-getter=3}",
    );
}

#[test]
fn triple_quad_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("flag_set", "flag == 1"));
    ctx.push_obligation(ProofObligation::assert(
        "triple_quad_active",
        "if flag == 1 { 1 } else { 0 } == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "QMS triple-quad flag=1 implies active");
}
