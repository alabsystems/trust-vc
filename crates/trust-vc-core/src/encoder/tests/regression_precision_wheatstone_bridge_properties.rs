// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Precision Wheatstone bridge property regression tests.
//!
//! Each test assumes a bounded property of a Wheatstone bridge measurement parameter
//! and asserts the same condition, verifying that the ay backend correctly
//! handles the assume-then-assert identity for these domain-specific ranges.

use super::*;

/// Resistance range: 1-10000000 ohms.
#[test]
fn test_wheatstone_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("r_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "r_bounds",
        "r_range >= 1 && r_range <= 10000000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "r_check",
        "r_range >= 1 && r_range <= 10000000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wheatstone bridge resistance in [1, 10000000] ohms",
    );
}

/// Accuracy scaled by 10000 (0.0001% resolution), range 1-500.
#[test]
fn test_wheatstone_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_bounds",
        "acc_x10000 >= 1 && acc_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_check",
        "acc_x10000 >= 1 && acc_x10000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wheatstone bridge accuracy x10000 in [1, 500]");
}

/// Ratio arms: 1-10000.
#[test]
fn test_wheatstone_ratio_arms_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_bounds",
        "ratio >= 1 && ratio <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_check",
        "ratio >= 1 && ratio <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wheatstone bridge ratio arms in [1, 10000]");
}

/// Sensitivity scaled by 1000 (0.001 uV/ohm resolution), range 1-10000.
#[test]
fn test_wheatstone_sensitivity_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sens_bounds",
        "sens_x1000 >= 1 && sens_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sens_check",
        "sens_x1000 >= 1 && sens_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wheatstone bridge sensitivity x1000 in [1, 10000]");
}

/// Excitation voltage scaled by 1000 (0.001V resolution), range 100-10000.
#[test]
fn test_wheatstone_excitation_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exc_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "exc_bounds",
        "exc_x1000 >= 100 && exc_x1000 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "exc_check",
        "exc_x1000 >= 100 && exc_x1000 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wheatstone bridge excitation x1000 in [100, 10000] V",
    );
}

/// Detector resolution: 1-1000 nV.
#[test]
fn test_wheatstone_detector_resolution_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("det_res", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "det_bounds",
        "det_res >= 1 && det_res <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "det_check",
        "det_res >= 1 && det_res <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wheatstone bridge detector resolution in [1, 1000] nV",
    );
}

/// Excitation type: 1=DC, 2=AC, 3=pulsed.
#[test]
fn test_wheatstone_excitation_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("exc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "exc_enum",
        "exc == 1 || exc == 2 || exc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "exc_check",
        "exc == 1 || exc == 2 || exc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wheatstone bridge excitation type in {1, 2, 3}");
}

/// Balance method: 1=manual, 2=auto, 3=digital.
#[test]
fn test_wheatstone_balance_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("bal", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "bal_enum",
        "bal == 1 || bal == 2 || bal == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "bal_check",
        "bal == 1 || bal == 2 || bal == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wheatstone bridge balance method in {1, 2, 3}");
}

/// Guard terminal: 1=none, 2=Wagner ground, 3=driven guard.
#[test]
fn test_wheatstone_guard_terminal_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("guard", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "guard_enum",
        "guard == 1 || guard == 2 || guard == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "guard_check",
        "guard == 1 || guard == 2 || guard == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Wheatstone bridge guard terminal in {1, 2, 3}");
}

/// Thermocouple compensation: boolean flag (0=disabled, 1=enabled).
#[test]
fn test_wheatstone_thermocouple_compensation_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tc", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc_bool", "tc == 0 || tc == 1"));
    ctx.push_obligation(ProofObligation::assert("tc_check", "tc == 0 || tc == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Wheatstone bridge thermocouple compensation in {0, 1}",
    );
}
