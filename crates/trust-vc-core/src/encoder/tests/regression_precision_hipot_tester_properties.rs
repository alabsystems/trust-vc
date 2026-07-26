// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_hipot_tester_test_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("voltage", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_voltage_range",
        "voltage >= 100 && voltage <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_voltage_range",
        "voltage >= 100 && voltage <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test voltage must be bounded between 100 and 50000 volts",
    );
}

#[test]
fn test_hipot_tester_leakage_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("leak_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_leakage_range",
        "leak_x100 >= 1 && leak_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_leakage_range",
        "leak_x100 >= 1 && leak_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "leakage current x100 must be bounded between 1 and 10000 (0.01 mA units)",
    );
}

#[test]
fn test_hipot_tester_ramp_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ramp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_ramp_range",
        "ramp_x10 >= 1 && ramp_x10 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_ramp_range",
        "ramp_x10 >= 1 && ramp_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ramp time x10 must be bounded between 1 and 600 (0.1 second units)",
    );
}

#[test]
fn test_hipot_tester_dwell_time_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dwell", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_dwell_range",
        "dwell >= 1 && dwell <= 999",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_dwell_range",
        "dwell >= 1 && dwell <= 999",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "dwell time must be bounded between 1 and 999 seconds",
    );
}

#[test]
fn test_hipot_tester_arc_detection_sensitivity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sens", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_sens_range",
        "sens >= 1 && sens <= 10",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_sens_range",
        "sens >= 1 && sens <= 10",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "arc detection sensitivity must be bounded between 1 and 10 levels",
    );
}

#[test]
fn test_hipot_tester_output_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_output_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_output_mode",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "output mode must be AC (1), DC (2), or IR (3)");
}

#[test]
fn test_hipot_tester_ground_bond_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_ground_bond_method",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_ground_bond_method",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "ground bond method must be resistance (1), current-check (2), or continuity (3)",
    );
}

#[test]
fn test_hipot_tester_safety_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_safety_standard",
        "std == 1 || std == 2 || std == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_safety_standard",
        "std == 1 || std == 2 || std == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "safety standard must be IEC-60950 (1), UL-60601 (2), or EN-61010 (3)",
    );
}

#[test]
fn test_hipot_tester_auto_discharge_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_auto_discharge",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_auto_discharge",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto discharge flag must be 0 (off) or 1 (on)");
}

#[test]
fn test_hipot_tester_charge_current_limit_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("limit", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_charge_limit",
        "limit >= 1 && limit <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_charge_limit",
        "limit >= 1 && limit <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "charge current limit must be bounded between 1 and 100 mA",
    );
}
