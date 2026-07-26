// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_winding_temperature_tester_resistance_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resist_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "resist_range",
        "resist_x1000 >= 1 && resist_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "resist_bounded",
        "resist_x1000 >= 1 && resist_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resistance x1000 must be in range 1-100000 representing 0.001-100.000 ohms",
    );
}

#[test]
fn test_winding_temperature_tester_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 50 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 50 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature offset +100 must be in range 50-350 representing -50 to 250 degrees C",
    );
}

#[test]
fn test_winding_temperature_tester_current_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_range",
        "curr_x1000 >= 1 && curr_x1000 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curr_bounded",
        "curr_x1000 >= 1 && curr_x1000 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "current x1000 must be in range 1-50000 representing 0.001-50.000 A",
    );
}

#[test]
fn test_winding_temperature_tester_voltage_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volt_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "volt_range",
        "volt_x100 >= 1 && volt_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "volt_bounded",
        "volt_x100 >= 1 && volt_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "voltage x100 must be in range 1-100000 representing 0.01-1000.00 V",
    );
}

#[test]
fn test_winding_temperature_tester_accuracy_x10000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x10000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x10000 >= 1 && acc_x10000 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "acc_x10000 >= 1 && acc_x10000 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x10000 must be in range 1-500 representing 0.0001-0.0500 percent",
    );
}

#[test]
fn test_winding_temperature_tester_sampling_rate_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "rate >= 1 && rate <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_bounded",
        "rate >= 1 && rate <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "sampling rate must be between 1 and 1000 Hz");
}

#[test]
fn test_winding_temperature_tester_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("material", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "material_range",
        "material == 1 || material == 2 || material == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "material_valid",
        "material == 1 || material == 2 || material == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "winding material must be copper (1), aluminum (2), or alloy (3)",
    );
}

#[test]
fn test_winding_temperature_tester_mode_three_way() {
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
        "test mode must be dc-resistance (1), hot-spot (2), or thermal-image (3)",
    );
}

#[test]
fn test_winding_temperature_tester_connection_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("conn", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "conn_range",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "conn_valid",
        "conn == 1 || conn == 2 || conn == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "connection config must be 2-wire (1), 4-wire (2), or kelvin (3)",
    );
}

#[test]
fn test_winding_temperature_tester_auto_temp_comp_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_range",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "auto temperature compensation flag must be 0 (disabled) or 1 (enabled)",
    );
}
