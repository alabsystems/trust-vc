// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn discharge_pressure_range_x10_bar() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_check",
        "press_x10 >= 10 && press_x10 <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure 1.0-15.0 bar scaled x10");
}

#[test]
fn oil_temperature_offset_plus_100() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_temp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "oil_temp >= 120 && oil_temp <= 220",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_check",
        "oil_temp >= 120 && oil_temp <= 220",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oil temperature 20-120C offset by +100");
}

#[test]
fn motor_speed_rpm_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 500 && speed <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_check",
        "speed >= 500 && speed <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor speed 500-5000 RPM");
}

#[test]
fn oil_injection_rate_x100_lpm() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_rate", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "rate_range",
        "oil_rate >= 1 && oil_rate <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "rate_check",
        "oil_rate >= 1 && oil_rate <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oil injection rate 0.01-50.00 L/min scaled x100");
}

#[test]
fn displacement_x10_cc_per_rev() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disp_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "disp_range",
        "disp_x10 >= 50 && disp_x10 <= 100000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "disp_check",
        "disp_x10 >= 50 && disp_x10 <= 100000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "displacement 5.0-10000.0 cc/rev scaled x10");
}

#[test]
fn vane_count_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vanes", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "vanes_range",
        "vanes >= 4 && vanes <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "vanes_check",
        "vanes >= 4 && vanes <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vane count 4-16");
}

#[test]
fn oil_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_enum",
        "oil == 1 || oil == 2 || oil == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_check",
        "oil == 1 || oil == 2 || oil == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oil type mineral/synthetic/PAO");
}

#[test]
fn vane_material_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("vane_mat", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "mat_enum",
        "vane_mat == 1 || vane_mat == 2 || vane_mat == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "mat_check",
        "vane_mat == 1 || vane_mat == 2 || vane_mat == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "vane material phenolic/PEEK/carbon");
}

#[test]
fn capacity_control_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_enum",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ctrl_check",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "capacity control modulation/on-off/variable-speed");
}

#[test]
fn auto_oil_separator_boolean() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flag_bool",
        "flag == 0 || flag == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flag_check",
        "flag == 0 || flag == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto oil separator on/off boolean");
}
