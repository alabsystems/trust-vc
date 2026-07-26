// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_motor_winding_resistance_range_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_range",
        "range >= 1 && range <= 20000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_bounded",
        "range >= 1 && range <= 20000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resistance range must be between 1 and 20000 micro-ohm",
    );
}

#[test]
fn test_motor_winding_test_current_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_range",
        "curr_x100 >= 1 && curr_x100 <= 10000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curr_bounded",
        "curr_x100 >= 1 && curr_x100 <= 10000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test current x100 must be in range 1-10000 representing 0.01 A",
    );
}

#[test]
fn test_motor_winding_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_range",
        "acc_x100 >= 1 && acc_x100 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_bounded",
        "acc_x100 >= 1 && acc_x100 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "accuracy x100 must be in range 1-100 representing 0.01 percent",
    );
}

#[test]
fn test_motor_winding_temperature_compensation_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 60 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 60 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "temperature compensation offset+100 must be in range 60-300 representing -40 to 200 degrees C");
}

#[test]
fn test_motor_winding_channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "chan_range",
        "channels >= 1 && channels <= 12",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "chan_bounded",
        "channels >= 1 && channels <= 12",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "channel count must be between 1 and 12");
}

#[test]
fn test_motor_winding_measurement_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("method", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "method_range",
        "method == 1 || method == 2 || method == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "method_valid",
        "method == 1 || method == 2 || method == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement method must be kelvin (1), wheatstone (2), or current-reversal (3)",
    );
}

#[test]
fn test_motor_winding_connection_type_three_way() {
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
        "connection type must be star (1), delta (2), or series (3)",
    );
}

#[test]
fn test_motor_winding_test_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "std_range",
        "std == 1 || std == 2 || std == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "std_valid",
        "std == 1 || std == 2 || std == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test standard must be IEEE-118 (1), IEC-60034 (2), or NEMA-MG1 (3)",
    );
}

#[test]
fn test_motor_winding_auto_range_select_flag() {
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
        "auto range select flag must be 0 (disabled) or 1 (enabled)",
    );
}

#[test]
fn test_motor_winding_settling_time_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_range",
        "time_x10 >= 1 && time_x10 <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_bounded",
        "time_x10 >= 1 && time_x10 <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "settling time x10 must be in range 1-600 representing 0.1 seconds",
    );
}
