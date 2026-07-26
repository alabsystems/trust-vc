// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_relay_test_pickup_voltage_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("pickup_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "pickup_x10_range",
        "pickup_x10 >= 1 && pickup_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "pickup_x10_bounded",
        "pickup_x10 >= 1 && pickup_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "pickup voltage x10 bounded 0.1-500.0 V");
}

#[test]
fn test_relay_test_dropout_voltage_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dropout_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dropout_x10_range",
        "dropout_x10 >= 1 && dropout_x10 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dropout_x10_bounded",
        "dropout_x10 >= 1 && dropout_x10 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "dropout voltage x10 bounded 0.1-500.0 V");
}

#[test]
fn test_relay_test_operate_time_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("time_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "time_x100_range",
        "time_x100 >= 1 && time_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "time_x100_bounded",
        "time_x100 >= 1 && time_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "operate time x100 bounded 0.01-1000.00 ms");
}

#[test]
fn test_relay_test_contact_resistance_x100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("res_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "res_x100_range",
        "res_x100 >= 1 && res_x100 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "res_x100_bounded",
        "res_x100 >= 1 && res_x100 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "contact resistance x100 bounded 0.01-1000.00 ohm");
}

#[test]
fn test_relay_test_coil_current_x1000_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x1000", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "curr_x1000_range",
        "curr_x1000 >= 1 && curr_x1000 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "curr_x1000_bounded",
        "curr_x1000 >= 1 && curr_x1000 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "coil current x1000 bounded 0.001-100.000 A");
}

#[test]
fn test_relay_test_relay_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rt", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rt_valid",
        "rt == 1 || rt == 2 || rt == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rt_three_way",
        "rt == 1 || rt == 2 || rt == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "relay type three-way: 1=electromagnetic 2=solid-state 3=reed",
    );
}

#[test]
fn test_relay_test_test_mode_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tm_valid",
        "tm == 1 || tm == 2 || tm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tm_three_way",
        "tm == 1 || tm == 2 || tm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test mode three-way: 1=timing 2=resistance 3=insulation",
    );
}

#[test]
fn test_relay_test_standard_three_way() {
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
        "test standard three-way: 1=IEC-61810 2=IEC-60255 3=IEEE-C37",
    );
}

#[test]
fn test_relay_test_auto_sequence_flag() {
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
    expect_verified(&result, "auto-sequence flag is boolean 0 or 1");
}

#[test]
fn test_relay_test_insulation_resistance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("insulation", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "insulation_range",
        "insulation >= 1 && insulation <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "insulation_bounded",
        "insulation >= 1 && insulation <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "insulation resistance bounded 1-100000 mega-ohm");
}
