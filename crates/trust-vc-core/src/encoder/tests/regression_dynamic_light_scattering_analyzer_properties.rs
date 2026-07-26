// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Dynamic light scattering (DLS) analyzer property regression tests.
//!
//! Each test assumes a domain constraint on an instrument parameter and
//! asserts the same constraint, locking the encoder's ability to round-trip
//! bounded-range and disjunctive properties for DLS instruments.

use super::*;

/// Test 1: Minimum particle size x10 nm (0.1 nm resolution) — bounded [1, 100].
#[test]
fn test_dls_size_range_min_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sz_min_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sz_min_x10 >= 1 && sz_min_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "sz_min_x10 >= 1 && sz_min_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "min particle size x10 in [1, 100]");
}

/// Test 2: Maximum particle size nm — bounded [1000, 100000].
#[test]
fn test_dls_size_range_max_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sz_max", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "sz_max >= 1000 && sz_max <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "sz_max >= 1000 && sz_max <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "max particle size in [1000, 100000] nm");
}

/// Test 3: Laser wavelength nm — bounded [400, 900].
#[test]
fn test_dls_laser_wavelength_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wl", i32_ty());
    ctx.push_obligation(ProofObligation::assume("range", "wl >= 400 && wl <= 900"));
    ctx.push_obligation(ProofObligation::assert("check", "wl >= 400 && wl <= 900"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser wavelength in [400, 900] nm");
}

/// Test 4: Laser power x10 mW (0.1 mW resolution) — bounded [10, 1000].
#[test]
fn test_dls_laser_power_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pwr_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "pwr_x10 >= 10 && pwr_x10 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "pwr_x10 >= 10 && pwr_x10 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "laser power x10 in [10, 1000]");
}

/// Test 5: Detection angle degrees — bounded [10, 175].
#[test]
fn test_dls_detection_angle_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("angle", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "angle >= 10 && angle <= 175",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "angle >= 10 && angle <= 175",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "detection angle in [10, 175] degrees");
}

/// Test 6: Sample volume x10 uL (0.1 uL resolution) — bounded [5, 10000].
#[test]
fn test_dls_sample_volume_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vol_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range",
        "vol_x10 >= 5 && vol_x10 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "vol_x10 >= 5 && vol_x10 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sample volume x10 in [5, 10000]");
}

/// Test 7: Correlator type — 3-way disjunction (1=linear, 2=log, 3=multi-tau).
#[test]
fn test_dls_correlator_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("corr", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "domain",
        "corr == 1 || corr == 2 || corr == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "corr == 1 || corr == 2 || corr == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "correlator type is valid 3-way disjunction");
}

/// Test 8: Cuvette type — 3-way disjunction (1=glass, 2=quartz, 3=disposable).
#[test]
fn test_dls_cuvette_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cuv", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "domain",
        "cuv == 1 || cuv == 2 || cuv == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "cuv == 1 || cuv == 2 || cuv == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cuvette type is valid 3-way disjunction");
}

/// Test 9: Analysis method — 3-way disjunction (1=cumulants, 2=CONTIN, 3=NNLS).
#[test]
fn test_dls_analysis_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "domain",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "check",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "analysis method is valid 3-way disjunction");
}

/// Test 10: Temperature control flag — boolean (0 or 1).
#[test]
fn test_dls_temperature_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("domain", "tc == 0 || tc == 1"));
    ctx.push_obligation(ProofObligation::assert("check", "tc == 0 || tc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temperature control flag is boolean (0 or 1)");
}
