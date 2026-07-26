// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
use super::*;

#[test]
fn resistance_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("resistance_ohm", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("r", "resistance_ohm == 10000")); // 10kΩ
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if resistance_ohm >= 100 && resistance_ohm <= 1000000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: 10kΩ in [100, 1000000]");
}

#[test]
fn resolution_steps_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("steps", u32_ty());
    ctx.declare_var_typed("valid", i32_ty());
    // Non-sequential valid resolutions: 64, 128, 256, 1024
    ctx.push_obligation(ProofObligation::assume("s", "steps == 256"));
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if steps == 64 || steps == 128 || steps == 256 || steps == 1024 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: 256 steps in {64,128,256,1024}");
}

#[test]
fn taper_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("taper", u32_ty()); // 1=linear, 2=logarithmic, 3=reverse log
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("t", "taper == 2")); // logarithmic
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if taper == 1 || taper == 2 || taper == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: taper 2 (log) in {1,2,3}");
}

#[test]
fn interface_type_valid() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("iface", u32_ty()); // 1=SPI, 2=I2C, 3=up/down
    ctx.declare_var_typed("valid", i32_ty());
    ctx.push_obligation(ProofObligation::assume("i", "iface == 1")); // SPI
    ctx.push_obligation(ProofObligation::assume(
        "v_def",
        "valid == if iface == 1 || iface == 2 || iface == 3 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: interface 1 (SPI) in {1,2,3}");
}

#[test]
fn supply_voltage_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("supply_mv", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("sv", "supply_mv == 3300")); // 3.3V
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if supply_mv >= 1800 && supply_mv <= 5500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: 3300mV supply in [1800, 5500]");
}

#[test]
fn wiper_current_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("wiper_current_ua", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("wc", "wiper_current_ua == 500")); // 500μA
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if wiper_current_ua >= 1 && wiper_current_ua <= 10000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: 500μA wiper current in [1, 10000]");
}

#[test]
fn channel_count_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("channels", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("ch", "channels == 4")); // quad digipot
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if channels >= 1 && channels <= 8 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: 4 channels in [1, 8]");
}

#[test]
fn temperature_coefficient_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("tempco_x10", u32_ty()); // 3.5 ppm/°C → 35
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("tc", "tempco_x10 == 35")); // 3.5 ppm/°C
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if tempco_x10 >= 1 && tempco_x10 <= 500 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: tempco 35 (3.5 ppm/°C) in [1, 500]");
}

#[test]
fn operating_temperature_bounded() {
    // Offset +500: real -40°C → 460, real 85°C → 585
    // Range [250, 1000] represents [-250°C, +500°C] absolute bounds
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("temp_offset", u32_ty());
    ctx.declare_var_typed("in_range", i32_ty());
    ctx.push_obligation(ProofObligation::assume("to", "temp_offset == 520")); // 20°C → 520
    ctx.push_obligation(ProofObligation::assume(
        "ir_def",
        "in_range == if temp_offset >= 250 && temp_offset <= 1000 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "in_range == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: temp 520 (20°C) in [250, 1000]");
}

#[test]
fn non_volatile_memory_flag() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("has_nvm", i32_ty()); // boolean: 0 or 1
    ctx.declare_var_typed("valid_flag", i32_ty());
    ctx.push_obligation(ProofObligation::assume("nvm", "has_nvm == 1")); // NVM present
    ctx.push_obligation(ProofObligation::assume(
        "vf_def",
        "valid_flag == if has_nvm == 0 || has_nvm == 1 { 1 } else { 0 }",
    ));
    ctx.push_obligation(ProofObligation::assert("ok", "valid_flag == 1"));
    ctx.push_obligation(ProofObligation::assert("is_set", "has_nvm == 1"));
    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "digipot: NVM flag 1 is valid boolean");
}
