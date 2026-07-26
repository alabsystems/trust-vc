// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_ammonia_compressor_motor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1000 && speed <= 3600",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1000 && speed <= 3600",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor speed must be between 1000 and 3600 RPM");
}

#[test]
fn test_ammonia_compressor_capacity_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cap", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cap_range",
        "cap >= 50 && cap <= 5000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cap_bounded",
        "cap >= 50 && cap <= 5000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "refrigeration capacity must be between 50 and 5000 kW",
    );
}

#[test]
fn test_ammonia_compressor_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 200",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 10 && press_x10 <= 200",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge pressure x10 must be in range 10-200 representing 1.0-20.0 bar",
    );
}

#[test]
fn test_ammonia_compressor_suction_temp_offset_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 50 && temp_off <= 150",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 50 && temp_off <= 150",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "suction temperature offset+100 must be in range 50-150 representing -50 to 50 C",
    );
}

#[test]
fn test_ammonia_compressor_oil_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oil_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oil_range",
        "oil_x10 >= 10 && oil_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oil_bounded",
        "oil_x10 >= 10 && oil_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil pressure x10 must be in range 10-100 representing 1.0-10.0 bar",
    );
}

#[test]
fn test_ammonia_compressor_cylinders_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cyl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cyl_range",
        "cyl >= 2 && cyl <= 16",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cyl_bounded",
        "cyl >= 2 && cyl <= 16",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "number of cylinders must be between 2 and 16");
}

#[test]
fn test_ammonia_compressor_type_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctype", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctype_range",
        "ctype == 1 || ctype == 2 || ctype == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ctype_valid",
        "ctype == 1 || ctype == 2 || ctype == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "compressor type must be reciprocating (1), screw (2), or rotary-vane (3)",
    );
}

#[test]
fn test_ammonia_compressor_capacity_control_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ctrl", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ctrl_range",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ctrl_valid",
        "ctrl == 1 || ctrl == 2 || ctrl == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "capacity control must be slide-valve (1), cylinder-unloading (2), or VFD (3)",
    );
}

#[test]
fn test_ammonia_compressor_oil_separator_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("sep", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "sep_range",
        "sep == 1 || sep == 2 || sep == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "sep_valid",
        "sep == 1 || sep == 2 || sep == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "oil separator type must be coalescent (1), demister (2), or centrifugal (3)",
    );
}

#[test]
fn test_ammonia_compressor_auto_oil_return_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("oret", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "oret_range",
        "oret == 0 || oret == 1",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "oret_valid",
        "oret == 0 || oret == 1",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "automatic oil return flag must be 0 (disabled) or 1 (enabled)",
    );
}
