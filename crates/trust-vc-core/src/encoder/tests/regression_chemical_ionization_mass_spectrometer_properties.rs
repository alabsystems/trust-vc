// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ci_ms_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mass", i32_ty());
    ctx.push_obligation(ProofObligation::assume("mr_a", "mass >= 1 && mass <= 2000"));
    ctx.push_obligation(ProofObligation::assert("mr_c", "mass >= 1 && mass <= 2000"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS mass range bounded");
}

#[test]
fn test_ci_ms_reagent_pressure_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rp_a",
        "press_x100 >= 1 && press_x100 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rp_c",
        "press_x100 >= 1 && press_x100 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS reagent gas pressure x100 bounded");
}

#[test]
fn test_ci_ms_source_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "st_a",
        "temp_off >= 150 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "st_c",
        "temp_off >= 150 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS ion source temperature offset bounded");
}

#[test]
fn test_ci_ms_electron_energy_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("energy", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ee_a",
        "energy >= 10 && energy <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ee_c",
        "energy >= 10 && energy <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS electron energy bounded");
}

#[test]
fn test_ci_ms_emission_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ec_a",
        "curr_x100 >= 1 && curr_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ec_c",
        "curr_x100 >= 1 && curr_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS emission current x100 bounded");
}

#[test]
fn test_ci_ms_sensitivity_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sn_a",
        "sens_x1000 >= 1 && sens_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sn_c",
        "sens_x1000 >= 1 && sens_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS sensitivity x1000 bounded");
}

#[test]
fn test_ci_ms_reagent_gas_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reagent", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rg_a",
        "reagent == 1 || reagent == 2 || reagent == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rg_c",
        "reagent == 1 || reagent == 2 || reagent == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS reagent gas three-way disjunction");
}

#[test]
fn test_ci_ms_analyzer_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("analyzer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "an_a",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "an_c",
        "analyzer == 1 || analyzer == 2 || analyzer == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS analyzer three-way disjunction");
}

#[test]
fn test_ci_ms_ionization_polarity_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("polarity", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ip_a",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ip_c",
        "polarity == 1 || polarity == 2 || polarity == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS ionization polarity three-way disjunction");
}

#[test]
fn test_ci_ms_auto_reagent_flow_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("rf_a", "flag == 0 || flag == 1"));
    ctx.push_obligation(ProofObligation::assert("rf_c", "flag == 0 || flag == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "CI-MS auto reagent flow flag");
}
