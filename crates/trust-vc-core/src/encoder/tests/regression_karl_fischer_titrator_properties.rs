//! Karl Fischer titrator property regression tests.
//!
//! These tests model integer-scaled physical parameters of a Karl Fischer
//! moisture titration system and verify that assumed ranges are preserved.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_kf_moisture_range_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_bound",
        "range >= 1 && range <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_ok",
        "range >= 1 && range <= 100",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "moisture range 1-100% water should stay bounded");
}

#[test]
fn test_kf_resolution_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_bound",
        "res_x1000 >= 1 && res_x1000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_ok",
        "res_x1000 >= 1 && res_x1000 <= 1000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "resolution x1000 ug should stay bounded");
}

#[test]
fn test_kf_sample_size_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("samp_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "samp_bound",
        "samp_x100 >= 1 && samp_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "samp_ok",
        "samp_x100 >= 1 && samp_x100 <= 10000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample size x100 g should stay bounded");
}

#[test]
fn test_kf_burette_volume_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bur_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bur_bound",
        "bur_x10 >= 10 && bur_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bur_ok",
        "bur_x10 >= 10 && bur_x10 <= 500",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "burette volume x10 mL should stay bounded");
}

#[test]
fn test_kf_drift_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("drift_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "drift_bound",
        "drift_x100 >= 1 && drift_x100 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "drift_ok",
        "drift_x100 >= 1 && drift_x100 <= 1000",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drift x100 ug/min should stay bounded");
}

#[test]
fn test_kf_electrode_sensitivity_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("elec_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "elec_bound",
        "elec_x1000 >= 1 && elec_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "elec_ok",
        "elec_x1000 >= 1 && elec_x1000 <= 500",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "electrode sensitivity x1000 mV should stay bounded",
    );
}

#[test]
fn test_kf_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "method_enum",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "method_ok",
        "method == 1 || method == 2 || method == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "method volumetric/coulometric/oven should stay valid",
    );
}

#[test]
fn test_kf_solvent_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("solv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "solv_enum",
        "solv == 1 || solv == 2 || solv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "solv_ok",
        "solv == 1 || solv == 2 || solv == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "solvent methanol/ethanol/chloroform should stay valid",
    );
}

#[test]
fn test_kf_endpoint_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ep", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ep_enum",
        "ep == 1 || ep == 2 || ep == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ep_ok",
        "ep == 1 || ep == 2 || ep == 3",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "endpoint potentiometric/amperometric/photometric should stay valid",
    );
}

#[test]
fn test_kf_autosampler_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_s", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_enum",
        "auto_s == 0 || auto_s == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_ok",
        "auto_s == 0 || auto_s == 1",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "autosampler boolean flag should stay valid");
}
