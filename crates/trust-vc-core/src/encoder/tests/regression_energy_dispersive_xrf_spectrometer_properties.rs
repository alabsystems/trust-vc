// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ed_xrf_tube_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 5 && voltage <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 5 && voltage <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube voltage must be between 5 and 60 kV");
}

#[test]
fn test_ed_xrf_tube_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current >= 1 && current <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_bounded",
        "current >= 1 && current <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "tube current must be between 1 and 2000 uA");
}

#[test]
fn test_ed_xrf_detectable_elements_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elements", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elements_range",
        "elements >= 1 && elements <= 83",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elements_bounded",
        "elements >= 1 && elements <= 83",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detectable elements must be between 1 and 83");
}

#[test]
fn test_ed_xrf_energy_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resolution_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resolution_range",
        "resolution_x10 >= 100 && resolution_x10 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resolution_bounded",
        "resolution_x10 >= 100 && resolution_x10 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "energy resolution x10 must be between 100 and 2000 representing 10.0-200.0 eV",
    );
}

#[test]
fn test_ed_xrf_detection_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "limit_range",
        "limit_x100 >= 1 && limit_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "limit_bounded",
        "limit_x100 >= 1 && limit_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detection limit x100 must be between 1 and 10000 representing 0.01-100.00 ppm",
    );
}

#[test]
fn test_ed_xrf_measurement_positions_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("positions", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "positions_range",
        "positions >= 1 && positions <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "positions_bounded",
        "positions >= 1 && positions <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "measurement positions must be between 1 and 20");
}

#[test]
fn test_ed_xrf_tube_target_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("target", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "target_valid",
        "target == 1 || target == 2 || target == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "target_is_known",
        "target == 1 || target == 2 || target == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tube target must be rhodium (1), molybdenum (2), or tungsten (3)",
    );
}

#[test]
fn test_ed_xrf_detector_type_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("detector", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "detector_valid",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "detector_is_known",
        "detector == 1 || detector == 2 || detector == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "detector must be SDD (1), Si-PIN (2), or proportional-counter (3)",
    );
}

#[test]
fn test_ed_xrf_sample_atmosphere_disjunction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("atmosphere", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "atmosphere_valid",
        "atmosphere == 1 || atmosphere == 2 || atmosphere == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "atmosphere_is_known",
        "atmosphere == 1 || atmosphere == 2 || atmosphere == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "sample atmosphere must be air (1), vacuum (2), or helium (3)",
    );
}

#[test]
fn test_ed_xrf_auto_sample_changer_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_changer", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "boolean_flag",
        "auto_changer == 0 || auto_changer == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "is_boolean",
        "auto_changer == 0 || auto_changer == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic sample changer flag must be 0 (off) or 1 (on)",
    );
}
