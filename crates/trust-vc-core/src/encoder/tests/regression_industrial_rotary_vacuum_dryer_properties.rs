// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_rotary_vacuum_dryer_drum_volume_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("volume", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_volume_range",
        "volume >= 100 && volume <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_volume_range",
        "volume >= 100 && volume <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drum volume bounded between 100 and 50000 liters");
}

#[test]
fn test_rotary_vacuum_dryer_jacket_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_press_range",
        "press_x10 >= 10 && press_x10 <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_press_range",
        "press_x10 >= 10 && press_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "jacket pressure x10 bounded between 10 and 60");
}

#[test]
fn test_rotary_vacuum_dryer_rotation_speed_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("rpm_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_rpm_range",
        "rpm_x10 >= 5 && rpm_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_rpm_range",
        "rpm_x10 >= 5 && rpm_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotation speed x10 bounded between 5 and 100");
}

#[test]
fn test_rotary_vacuum_dryer_vacuum_level_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vacuum", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_vacuum_range",
        "vacuum >= 1 && vacuum <= 1000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_vacuum_range",
        "vacuum >= 1 && vacuum <= 1000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vacuum level bounded between 1 and 1000 mbar");
}

#[test]
fn test_rotary_vacuum_dryer_product_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_temp_range",
        "temp_off >= 50 && temp_off <= 300",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_temp_range",
        "temp_off >= 50 && temp_off <= 300",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "product temperature offset100 bounded between 50 and 300",
    );
}

#[test]
fn test_rotary_vacuum_dryer_heating_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("hm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_heating_method",
        "hm == 1 || hm == 2 || hm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_heating_method",
        "hm == 1 || hm == 2 || hm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "heating method is one of three types");
}

#[test]
fn test_rotary_vacuum_dryer_agitator_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("at", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_agitator_type",
        "at == 1 || at == 2 || at == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_agitator_type",
        "at == 1 || at == 2 || at == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "agitator type is one of three types");
}

#[test]
fn test_rotary_vacuum_dryer_discharge_mechanism_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_discharge_mechanism",
        "dm == 1 || dm == 2 || dm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_discharge_mechanism",
        "dm == 1 || dm == 2 || dm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge mechanism is one of three types");
}

#[test]
fn test_rotary_vacuum_dryer_auto_vacuum_control_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_flag_bool",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto vacuum control flag is boolean");
}

#[test]
fn test_rotary_vacuum_dryer_fill_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "assume_ratio_range",
        "ratio_x10 >= 1 && ratio_x10 <= 8",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "assert_ratio_range",
        "ratio_x10 >= 1 && ratio_x10 <= 8",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "fill ratio x10 bounded between 1 and 8");
}
