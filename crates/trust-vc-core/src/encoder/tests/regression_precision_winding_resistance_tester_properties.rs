// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_winding_resistance_tester_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current >= 1 && current <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_bounded",
        "current >= 1 && current <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test current must be between 1 and 100000 mA");
}

#[test]
fn test_winding_resistance_tester_range_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_range",
        "res_x100 >= 1 && res_x100 <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_bounded",
        "res_x100 >= 1 && res_x100 <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resistance range x100 must be in range 1-10000000 representing 0.01-100000.00 mohms",
    );
}

#[test]
fn test_winding_resistance_tester_channels_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("chan", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "chan_range",
        "chan >= 1 && chan <= 6",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "chan_bounded",
        "chan >= 1 && chan <= 6",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of channels must be between 1 and 6");
}

#[test]
fn test_winding_resistance_tester_accuracy_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x1000 >= 1 && acc_x1000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "acc_x1000 >= 1 && acc_x1000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x1000 must be in range 1-500 representing 0.001-0.500 percent",
    );
}

#[test]
fn test_winding_resistance_tester_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "voltage_range",
        "voltage >= 1 && voltage <= 50",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "voltage_bounded",
        "voltage >= 1 && voltage <= 50",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test voltage must be between 1 and 50 V");
}

#[test]
fn test_winding_resistance_tester_demag_cycles_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("demag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "demag_range",
        "demag >= 1 && demag <= 20",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "demag_bounded",
        "demag >= 1 && demag <= 20",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "demagnetization cycles must be between 1 and 20");
}

#[test]
fn test_winding_resistance_tester_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_range",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode must be continuous (1), single-shot (2), or tap-changer (3)",
    );
}

#[test]
fn test_winding_resistance_tester_winding_config_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("config", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "config_range",
        "config == 1 || config == 2 || config == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "config_valid",
        "config == 1 || config == 2 || config == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "winding configuration must be single-phase (1), three-phase-wye (2), or three-phase-delta (3)");
}

#[test]
fn test_winding_resistance_tester_temp_compensation_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("comp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "comp_range",
        "comp == 1 || comp == 2 || comp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "comp_valid",
        "comp == 1 || comp == 2 || comp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature compensation must be copper (1), aluminum (2), or manual (3)",
    );
}

#[test]
fn test_winding_resistance_tester_auto_demag_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("demag_f", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "demag_f_range",
        "demag_f == 0 || demag_f == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "demag_f_valid",
        "demag_f == 0 || demag_f == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic demagnetization flag must be 0 (disabled) or 1 (enabled)",
    );
}
