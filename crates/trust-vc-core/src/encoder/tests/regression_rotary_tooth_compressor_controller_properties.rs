// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn test_rotary_tooth_compressor_discharge_pressure_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("press_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "press_range",
        "press_x10 >= 10 && press_x10 <= 100",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "press_bounded",
        "press_x10 >= 10 && press_x10 <= 100",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "discharge pressure x10 bounded 0.1 bar");
}

#[test]
fn test_rotary_tooth_compressor_rotor_speed_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("speed", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "speed_range",
        "speed >= 1000 && speed <= 15000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "speed_bounded",
        "speed >= 1000 && speed <= 15000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "rotor speed bounded RPM");
}

#[test]
fn test_rotary_tooth_compressor_flow_rate_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("flow_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "flow_range",
        "flow_x10 >= 5 && flow_x10 <= 3000",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "flow_bounded",
        "flow_x10 >= 5 && flow_x10 <= 3000",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "flow rate x10 bounded 0.1 m3/min");
}

#[test]
fn test_rotary_tooth_compressor_motor_power_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("power", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "power_range",
        "power >= 5 && power <= 500",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "power_bounded",
        "power >= 5 && power <= 500",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "motor power bounded kW");
}

#[test]
fn test_rotary_tooth_compressor_discharge_temp_offset100_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_off", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "temp_range",
        "temp_off >= 150 && temp_off <= 350",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "temp_bounded",
        "temp_off >= 150 && temp_off <= 350",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "discharge temp offset+100 bounded represents 50-250C",
    );
}

#[test]
fn test_rotary_tooth_compressor_tooth_profile_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tp", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "tp_range",
        "tp == 1 || tp == 2 || tp == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "tp_valid",
        "tp == 1 || tp == 2 || tp == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "tooth profile three-way involute/cycloidal/straight",
    );
}

#[test]
fn test_rotary_tooth_compressor_cooling_method_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("cm", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "cm_range",
        "cm == 1 || cm == 2 || cm == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "cm_valid",
        "cm == 1 || cm == 2 || cm == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "cooling method three-way air/water/oil-injected");
}

#[test]
fn test_rotary_tooth_compressor_drive_coupling_three_way() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("dc", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "dc_range",
        "dc == 1 || dc == 2 || dc == 3",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "dc_valid",
        "dc == 1 || dc == 2 || dc == 3",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "drive coupling three-way direct/belt/gear");
}

#[test]
fn test_rotary_tooth_compressor_auto_speed_regulation_flag() {
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
    expect_verified(&result, "auto speed regulation boolean flag");
}

#[test]
fn test_rotary_tooth_compressor_compression_ratio_x10_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("ratio_x10", i32_ty());
    ctx.push_obligation(ProofObligation::assume(
        "ratio_range",
        "ratio_x10 >= 15 && ratio_x10 <= 60",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "ratio_bounded",
        "ratio_x10 >= 15 && ratio_x10 <= 60",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "compression ratio x10 bounded 0.1");
}
