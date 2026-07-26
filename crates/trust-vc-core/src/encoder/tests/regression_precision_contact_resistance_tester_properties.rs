// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_contact_resistance_test_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("current", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "current >= 10 && current <= 600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_bounded",
        "current >= 10 && current <= 600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test current bounded 10-600 amps DC");
}

#[test]
fn test_contact_resistance_range_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("range_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "range_x100_range",
        "range_x100 >= 1 && range_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "range_x100_bounded",
        "range_x100 >= 1 && range_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "resistance range x100 bounded 0.01 micro-ohm to 1000 micro-ohm",
    );
}

#[test]
fn test_contact_resistance_accuracy_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("acc_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "acc_x100_range",
        "acc_x100 >= 10 && acc_x100 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "acc_x100_bounded",
        "acc_x100 >= 10 && acc_x100 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "accuracy x100 bounded 0.10% to 5.00%");
}

#[test]
fn test_contact_resistance_duration_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("duration", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "duration_range",
        "duration >= 1 && duration <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "duration_bounded",
        "duration >= 1 && duration <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "test duration bounded 1-300 seconds");
}

#[test]
fn test_contact_resistance_temperature_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_off_range",
        "temp_off >= 60 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_off_bounded",
        "temp_off >= 60 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "temperature offset+100 bounded 60-300 represents -40 to 200 deg C",
    );
}

#[test]
fn test_contact_resistance_measurement_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("mode", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mode_valid",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mode_three_way",
        "mode == 1 || mode == 2 || mode == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "measurement mode three-way: 1=continuous 2=pulse 3=dual-polarity",
    );
}

#[test]
fn test_contact_resistance_probe_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("probe", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "probe_valid",
        "probe == 1 || probe == 2 || probe == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "probe_three_way",
        "probe == 1 || probe == 2 || probe == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "probe type three-way: 1=kelvin-clip 2=c-clamp 3=needle",
    );
}

#[test]
fn test_contact_resistance_test_standard_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("std", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "std_valid",
        "std == 1 || std == 2 || std == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "std_three_way",
        "std == 1 || std == 2 || std == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test standard three-way: 1=IEC-62271 2=ANSI-C37 3=IEEE-C57",
    );
}

#[test]
fn test_contact_resistance_auto_demagnetize_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_valid",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_boolean",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto-demagnetize flag is boolean 0 or 1");
}

#[test]
fn test_contact_resistance_voltage_drop_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vdrop_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vdrop_range",
        "vdrop_x1000 >= 1 && vdrop_x1000 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vdrop_bounded",
        "vdrop_x1000 >= 1 && vdrop_x1000 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "voltage drop x1000 bounded 0.001-50.000 mV");
}
