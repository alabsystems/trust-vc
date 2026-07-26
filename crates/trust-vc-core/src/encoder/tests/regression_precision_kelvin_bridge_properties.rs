// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Precision Kelvin bridge property regression tests.
//!
//! Each test assumes a bounded property of a Kelvin bridge measurement parameter
//! and asserts the same condition, verifying that the ay backend correctly
//! handles the assume-then-assert identity for these domain-specific ranges.

use super::*;

/// Resistance scaled by 10000 (0.0001 ohm resolution), range 1-10000000.
#[test]
fn test_kelvin_bridge_range_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("r_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "r_bounds",
        "r_x10000 >= 1 && r_x10000 <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "r_check",
        "r_x10000 >= 1 && r_x10000 <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge resistance x10000 in [1, 10000000]");
}

/// Accuracy scaled by 10000 (0.0001% resolution), range 1-200.
#[test]
fn test_kelvin_bridge_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_bounds",
        "acc_x10000 >= 1 && acc_x10000 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_check",
        "acc_x10000 >= 1 && acc_x10000 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge accuracy x10000 in [1, 200]");
}

/// Test current range: 1-100 A.
#[test]
fn test_kelvin_bridge_test_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cur", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cur_bounds",
        "cur >= 1 && cur <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cur_check",
        "cur >= 1 && cur <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge test current in [1, 100] A");
}

/// Voltage drop scaled by 1000 (0.001 mV resolution), range 1-10000.
#[test]
fn test_kelvin_bridge_voltage_drop_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vd_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vd_bounds",
        "vd_x1000 >= 1 && vd_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vd_check",
        "vd_x1000 >= 1 && vd_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge voltage drop x1000 in [1, 10000] mV");
}

/// Temperature scaled by 10 (0.1 C resolution), range 150-500.
#[test]
fn test_kelvin_bridge_temperature_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_bounds",
        "temp_x10 >= 150 && temp_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_check",
        "temp_x10 >= 150 && temp_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge temperature x10 in [150, 500] C");
}

/// Resolution scaled by 100000 (0.00001 ohm resolution), range 1-100.
#[test]
fn test_kelvin_bridge_resolution_x100000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_bounds",
        "res_x100000 >= 1 && res_x100000 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_check",
        "res_x100000 >= 1 && res_x100000 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge resolution x100000 in [1, 100]");
}

/// Connection type: 1=4-wire, 2=2-wire, 3=guarded.
#[test]
fn test_kelvin_bridge_connection_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conn_enum",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conn_check",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge connection type in {1, 2, 3}");
}

/// Current source type: 1=DC, 2=pulsed DC, 3=AC.
#[test]
fn test_kelvin_bridge_current_source_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("src", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "src_enum",
        "src == 1 || src == 2 || src == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "src_check",
        "src == 1 || src == 2 || src == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge current source in {1, 2, 3}");
}

/// Ranging mode: 1=auto, 2=manual, 3=fixed.
#[test]
fn test_kelvin_bridge_ranging_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rng", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rng_enum",
        "rng == 1 || rng == 2 || rng == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rng_check",
        "rng == 1 || rng == 2 || rng == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge ranging mode in {1, 2, 3}");
}

/// Thermal EMF compensation: boolean flag (0=disabled, 1=enabled).
#[test]
fn test_kelvin_bridge_thermal_emf_compensation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "comp_bool",
        "comp == 0 || comp == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "comp_check",
        "comp == 0 || comp == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Kelvin bridge thermal EMF compensation in {0, 1}");
}
