// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Precision LCR bridge property regression tests.
//!
//! Each test assumes a bounded property of an LCR bridge measurement parameter
//! and asserts the same condition, verifying that the ay backend correctly
//! handles the assume-then-assert identity for these domain-specific ranges.

use super::*;

/// Frequency range: 1 Hz to 2 MHz.
#[test]
fn test_lcr_bridge_frequency_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("freq", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "freq_bounds",
        "freq >= 1 && freq <= 2000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "freq_check",
        "freq >= 1 && freq <= 2000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge frequency in [1, 2000000] Hz");
}

/// Basic accuracy scaled by 10000 (0.0001% resolution), range 1-1000.
#[test]
fn test_lcr_bridge_basic_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_bounds",
        "acc_x10000 >= 1 && acc_x10000 <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_check",
        "acc_x10000 >= 1 && acc_x10000 <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge accuracy x10000 in [1, 1000]");
}

/// Capacitance scaled by 100 (0.01 pF resolution), range 1-1000000.
#[test]
fn test_lcr_bridge_capacitance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cap_bounds",
        "cap_x100 >= 1 && cap_x100 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cap_check",
        "cap_x100 >= 1 && cap_x100 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge capacitance x100 in [1, 1000000] pF");
}

/// Inductance scaled by 100 (0.01 uH resolution), range 1-1000000.
#[test]
fn test_lcr_bridge_inductance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ind_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ind_bounds",
        "ind_x100 >= 1 && ind_x100 <= 1000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ind_check",
        "ind_x100 >= 1 && ind_x100 <= 1000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge inductance x100 in [1, 1000000] uH");
}

/// Resistance range: 1 ohm to 100 Mohm.
#[test]
fn test_lcr_bridge_resistance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_bounds",
        "res >= 1 && res <= 100000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_check",
        "res >= 1 && res <= 100000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge resistance in [1, 100000000] ohms");
}

/// Test signal voltage scaled by 1000 (0.001 V resolution), range 5-2000.
#[test]
fn test_lcr_bridge_test_signal_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sig_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sig_bounds",
        "sig_x1000 >= 5 && sig_x1000 <= 2000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sig_check",
        "sig_x1000 >= 5 && sig_x1000 <= 2000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge test signal x1000 in [5, 2000] V");
}

/// Measurement speed: 1=slow, 2=medium, 3=fast.
#[test]
fn test_lcr_bridge_measurement_speed_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("spd", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "spd_enum",
        "spd == 1 || spd == 2 || spd == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "spd_check",
        "spd == 1 || spd == 2 || spd == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge measurement speed in {1, 2, 3}");
}

/// Circuit mode: 1=series, 2=parallel, 3=auto.
#[test]
fn test_lcr_bridge_circuit_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_enum",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_check",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge circuit mode in {1, 2, 3}");
}

/// Display parameter: 1=Cs-D, 2=Cp-D, 3=Ls-Q.
#[test]
fn test_lcr_bridge_display_param_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_enum",
        "disp == 1 || disp == 2 || disp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disp_check",
        "disp == 1 || disp == 2 || disp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge display param in {1, 2, 3}");
}

/// DC bias capability: boolean flag (0=disabled, 1=enabled).
#[test]
fn test_lcr_bridge_dc_bias_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bias", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bias_bool",
        "bias == 0 || bias == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bias_check",
        "bias == 0 || bias == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "LCR bridge DC bias flag in {0, 1}");
}
