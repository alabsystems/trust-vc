// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Precision digital bridge property regression tests.
//!
//! Each test assumes a bounded property of a digital bridge measurement parameter
//! and asserts the same condition, verifying that the ay backend correctly
//! handles the assume-then-assert identity for these domain-specific ranges.

use super::*;

/// Test frequency range: 1 MHz to 120 MHz.
#[test]
fn test_digital_bridge_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq_mhz", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_bounds",
        "freq_mhz >= 1 && freq_mhz <= 120",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_check",
        "freq_mhz >= 1 && freq_mhz <= 120",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital bridge frequency in [1, 120] MHz");
}

/// Impedance accuracy scaled by 1000 (0.001% resolution), range 1-500.
#[test]
fn test_digital_bridge_impedance_accuracy_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("imp_acc_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "imp_acc_bounds",
        "imp_acc_x1000 >= 1 && imp_acc_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "imp_acc_check",
        "imp_acc_x1000 >= 1 && imp_acc_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "digital bridge impedance accuracy x1000 in [1, 500]",
    );
}

/// Capacitance range code: 1 (pF) to 10 (mF).
#[test]
fn test_digital_bridge_capacitance_range_code_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cap_range_bounds",
        "cap_range >= 1 && cap_range <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cap_range_check",
        "cap_range >= 1 && cap_range <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital bridge capacitance range code in [1, 10]");
}

/// Resistance range code: 1 (milliohm) to 10 (megaohm).
#[test]
fn test_digital_bridge_resistance_range_code_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range_bounds",
        "res_range >= 1 && res_range <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_range_check",
        "res_range >= 1 && res_range <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital bridge resistance range code in [1, 10]");
}

/// Test signal level scaled by 1000 (0.001 V resolution), range 1-5000.
#[test]
fn test_digital_bridge_signal_level_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sig_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sig_bounds",
        "sig_x1000 >= 1 && sig_x1000 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sig_check",
        "sig_x1000 >= 1 && sig_x1000 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital bridge signal level x1000 in [1, 5000] V");
}

/// Bridge type: 1=auto-balance, 2=transformer-ratio, 3=RF-IV.
#[test]
fn test_digital_bridge_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("btype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "btype_enum",
        "btype == 1 || btype == 2 || btype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "btype_check",
        "btype == 1 || btype == 2 || btype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital bridge type in {1, 2, 3}");
}

/// Measurement parameter: 1=Z-theta, 2=Cs-D, 3=Ls-Q.
#[test]
fn test_digital_bridge_measurement_param_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mparam", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mparam_enum",
        "mparam == 1 || mparam == 2 || mparam == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mparam_check",
        "mparam == 1 || mparam == 2 || mparam == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital bridge measurement param in {1, 2, 3}");
}

/// Fixture type: 1=4-terminal, 2=4-terminal-pair, 3=coaxial.
#[test]
fn test_digital_bridge_fixture_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("fixture", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "fixture_enum",
        "fixture == 1 || fixture == 2 || fixture == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "fixture_check",
        "fixture == 1 || fixture == 2 || fixture == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digital bridge fixture type in {1, 2, 3}");
}

/// Measurement speed: 1 to 1000 readings per second.
#[test]
fn test_digital_bridge_measurement_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_bounds",
        "speed >= 1 && speed <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "speed >= 1 && speed <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "digital bridge measurement speed in [1, 1000] readings/s",
    );
}

/// DC bias superposition capability: boolean flag (0=disabled, 1=enabled).
#[test]
fn test_digital_bridge_dc_bias_superposition_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dc_bias", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dc_bias_bool",
        "dc_bias == 0 || dc_bias == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dc_bias_check",
        "dc_bias == 0 || dc_bias == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "digital bridge DC bias superposition flag in {0, 1}",
    );
}
