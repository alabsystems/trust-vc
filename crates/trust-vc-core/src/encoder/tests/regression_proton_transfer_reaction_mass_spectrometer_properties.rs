// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ptr_drift_tube_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drift_v", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dv_a",
        "drift_v >= 100 && drift_v <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dv_c",
        "drift_v >= 100 && drift_v <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drift tube voltage in [100, 1000] V");
}

#[test]
fn test_ptr_drift_tube_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drift_p_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dp_a",
        "drift_p_x10 >= 10 && drift_p_x10 <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dp_c",
        "drift_p_x10 >= 10 && drift_p_x10 <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "drift tube pressure x10 in [10, 50] representing 1.0-5.0 mbar",
    );
}

#[test]
fn test_ptr_drift_tube_temp_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drift_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dt_a",
        "drift_temp >= 40 && drift_temp <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dt_c",
        "drift_temp >= 40 && drift_temp <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drift tube temperature in [40, 200] C");
}

#[test]
fn test_ptr_e_over_n_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("en_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "en_a",
        "en_x10 >= 600 && en_x10 <= 2500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "en_c",
        "en_x10 >= 600 && en_x10 <= 2500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "E/N x10 in [600, 2500] representing 60.0-250.0 Td");
}

#[test]
fn test_ptr_mass_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mz_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mr_a",
        "mz_max >= 10 && mz_max <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mr_c",
        "mz_max >= 10 && mz_max <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "mass range in [10, 1000] m/z");
}

#[test]
fn test_ptr_sensitivity_ppbv_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sn_a",
        "sens_x100 >= 1 && sens_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sn_c",
        "sens_x100 >= 1 && sens_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sensitivity x100 in [1, 10000] representing 0.01-100.00 ppbv",
    );
}

#[test]
fn test_ptr_ion_source_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ion_src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "is_a",
        "ion_src == 1 || ion_src == 2 || ion_src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_c",
        "ion_src == 1 || ion_src == 2 || ion_src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ion source: hollow cathode, RF discharge, or microwave plasma",
    );
}

#[test]
fn test_ptr_analyzer_classification() {
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
    expect_verified(&result, "analyzer: quadrupole, time-of-flight, or ion trap");
}

#[test]
fn test_ptr_reagent_ion_classification() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("reagent", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ri_a",
        "reagent == 1 || reagent == 2 || reagent == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ri_c",
        "reagent == 1 || reagent == 2 || reagent == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "reagent ion: H3O+, NO+, or O2+");
}

#[test]
fn test_ptr_switchable_reagent_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("switchable", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sw_a",
        "switchable == 0 || switchable == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sw_c",
        "switchable == 0 || switchable == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "switchable reagent ion flag is boolean");
}
