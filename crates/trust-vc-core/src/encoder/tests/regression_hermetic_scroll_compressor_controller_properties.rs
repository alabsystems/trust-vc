// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_hermetic_scroll_compressor_suction_pressure_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "suction_range",
        "press_x10 >= 5 && press_x10 <= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "suction_positive",
        "press_x10 >= 5 && press_x10 <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "suction pressure x10 bar in [5, 150]");
}

#[test]
fn test_hermetic_scroll_compressor_discharge_pressure_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("disc_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "discharge_range",
        "disc_x10 >= 20 && disc_x10 <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "discharge_positive",
        "disc_x10 >= 20 && disc_x10 <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure x10 bar in [20, 500]");
}

#[test]
fn test_hermetic_scroll_compressor_motor_current_range() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("curr_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "current_range",
        "curr_x100 >= 10 && curr_x100 <= 50000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "current_positive",
        "curr_x100 >= 10 && curr_x100 <= 50000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor current x100 A in [10, 50000]");
}

#[test]
fn test_hermetic_scroll_compressor_discharge_temp_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 130 && temp_off <= 400",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_positive",
        "temp_off >= 130 && temp_off <= 400",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge temp offset +100 C in [130, 400]");
}

#[test]
fn test_hermetic_scroll_compressor_scroll_wrap_height() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wrap_x100", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "wrap_range",
        "wrap_x100 >= 50 && wrap_x100 <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "wrap_positive",
        "wrap_x100 >= 50 && wrap_x100 <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "scroll wrap height x100 mm in [50, 5000]");
}

#[test]
fn test_hermetic_scroll_compressor_oil_sump_temp_offset() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_range",
        "oil_off >= 100 && oil_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_positive",
        "oil_off >= 100 && oil_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "oil sump temp offset +100 C in [100, 350]");
}

#[test]
fn test_hermetic_scroll_compressor_refrigerant_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("refrigerant", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "refrigerant_valid",
        "refrigerant == 1 || refrigerant == 2 || refrigerant == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "refrigerant_in_range",
        "refrigerant >= 1 && refrigerant <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "refrigerant 3-way: 1=R410A, 2=R32, 3=R454B");
}

#[test]
fn test_hermetic_scroll_compressor_capacity_control() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap_ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cap_ctrl_valid",
        "cap_ctrl == 1 || cap_ctrl == 2 || cap_ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cap_ctrl_in_range",
        "cap_ctrl >= 1 && cap_ctrl <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity control 3-way: 1=inverter, 2=digital-scroll, 3=tandem",
    );
}

#[test]
fn test_hermetic_scroll_compressor_protection_mode() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("protection", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "protection_valid",
        "protection == 1 || protection == 2 || protection == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "protection_in_range",
        "protection >= 1 && protection <= 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "protection 3-way: 1=thermal-overload, 2=pressure-switch, 3=electronic-module",
    );
}

#[test]
fn test_hermetic_scroll_compressor_auto_superheat_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("auto_sh", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "auto_sh_bool",
        "auto_sh == 0 || auto_sh == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "auto_sh_bounded",
        "auto_sh >= 0 && auto_sh <= 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "auto superheat control boolean flag: 0 or 1");
}
